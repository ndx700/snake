package com.example.snake

import java.io.*
import java.util.concurrent.Executors
import java.util.concurrent.Future
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicLong
import java.util.zip.CRC32
import kotlin.math.abs
import kotlin.random.Random

/** Single owner of learner state: no Q-table locks, generation barriers or UI-thread training. */
class SnakeTrainer(private val file: File) : AutoCloseable {
    data class Actor(val score:Int=0,val length:Int=1,val hunger:Int=0,val region:Int=0,
        val tailSafe:Boolean=false,val reason:String="准备训练")
    data class Stats(val games: Long=0, val steps: Long=0, val best: Int=0,
        val mean: Float=0f, val validation: Float=0f, val championValidation: Float=0f,
        val updates: Long=0, val epsilon: Float=0.12f, val active: Boolean=false,
        val history: List<Int> = emptyList(), val deaths: List<Long> = listOf(0,0,0,0),
        val gamesPerMinute: Float=0f, val stepsPerSecond: Float=0f,
        val status: String="待命", val evaluations: Long=0, val actor:Actor=Actor(),
        val learningWeights:List<Float> = emptyList())
    private val executor=Executors.newSingleThreadExecutor { r -> Thread(r,"Snake-RL").apply { priority=Thread.NORM_PRIORITY-1 } }
    private val run=AtomicBoolean(false)
    private val session=AtomicLong(0)
    private var workingSession=0L
    private var task: Future<*>?=null
    private var closed=false
    private var learner=FloatArray(SnakePolicy.FEATURES)
    @Volatile private var champion=FloatArray(SnakePolicy.FEATURES)
    @Volatile var stats=Stats(); private set
    @Volatile var fast=false
    private var games=0L; private var totalSteps=0L; private var updates=0L
    private var best=0; private var championMean=-1f; private var validation=0f; private var evaluations=0L
    private val history=java.util.ArrayDeque<Int>()
    private val deaths=LongArray(4)
    private var saveError=""
    private var actor=Actor()
    init { load() }
    fun model(): FloatArray=champion.copyOf()
    @Synchronized fun start(highPower: Boolean=false) {
        if(closed) return
        fast=highPower
        if(run.getAndSet(true)) return
        val id=session.incrementAndGet()
        task=executor.submit { train(id) }
    }
    @Synchronized fun stop() {
        run.set(false);session.incrementAndGet()
        // Save is queued behind the learner; no UI blocking or stale worker write after restart.
        if(!closed) executor.submit { save(); if(!run.get()) publish(false,"已暂停") }
    }
    private fun alive()=run.get() && session.get()==workingSession && !Thread.currentThread().isInterrupted
    private fun train(id:Long) {
        workingSession=id
        val rng=Random.Default
        var lastPublish=System.nanoTime(); var lastYield=lastPublish; val start=lastPublish; val startGames=games; val startSteps=totalSteps
        try {
            if(championMean<0f && alive()) {
                publish(true,"基线评测中",start,startGames,startSteps)
                val baseline=evaluate(champion)
                if(baseline!=null) { championMean=baseline;validation=baseline;evaluations++;save() }
            }
            while(alive()) {
                var episodeSeed=rng.nextInt()
                while(episodeSeed in 710000 until 710016) episodeSeed=rng.nextInt()
                val g=SnakeEngine(seed=episodeSeed); val policy=SnakePolicy(g)
                val trace=FloatArray(SnakePolicy.FEATURES)
                val epsilon=(0.12f/(1f+games/2000f)).coerceAtLeast(0.015f)
                var current=policy.choose(learner,epsilon,rng)
                var ended=false
                while(alive() && !g.ended) {
                    val result=g.step(current.action); totalSteps++
                    ended=g.ended
                    val next=if(ended) null else policy.choose(learner,epsilon,rng)
                    // Actual eating, death and win rewards. No reward just for displaying statistics.
                    val reward=when {
                        g.cause=="WIN" -> result.coerceAtLeast(0)/100f+10f
                        result<0 -> -5f
                        result>0 -> result/100f
                        else -> -0.004f
                    }
                    val q=SnakePolicy.value(learner,current.features)
                    val target=reward + if(next==null) 0f else 0.99f*SnakePolicy.value(learner,next.features)
                    val delta=(target-q).coerceIn(-8f,8f)
                    var norm=1f
                    for(v in current.features) norm+=v*v
                    for(i in trace.indices) {
                        trace[i]=(trace[i]*0.99f*0.75f+current.features[i]).coerceIn(-4f,4f)
                        learner[i]=(learner[i]+0.025f/norm*delta*trace[i]).coerceIn(-16f,16f)
                    }
                    updates++
                    if(next!=null) current=next
                    val now=System.nanoTime()
                    if(now-lastPublish>=250_000_000L) {
                        actor=Actor(g.score,g.length,g.hunger,current.region,current.tailSafe,current.reason)
                        publish(true,"强化学习",start,startGames,startSteps); lastPublish=now
                    }
                    if(!fast && now-lastYield>=32_000_000L) { Thread.sleep(32);lastYield=System.nanoTime() }
                }
                if(ended) {
                    actor=Actor(g.score,g.length,g.hunger,current.region,current.tailSafe,current.reason)
                    games++; best=maxOf(best,g.score); history.addLast(g.score)
                    while(history.size>120) history.removeFirst()
                    deaths[when(g.cause) { "WALL"->0; "SELF"->1; "HUNGER"->2; else->3 }]++
                    if(games%64L==0L && alive()) {
                        publish(true,"独立评测中",start,startGames,startSteps)
                        val candidate=learner.copyOf()
                        val value=evaluate(candidate)
                        if(value!=null) {
                            validation=value; evaluations++
                            if(value>championMean+1f) { champion=candidate; championMean=value }
                            save()
                        }
                    }
                }
            }
            save(); if(!run.get()) publish(false,"已暂停")
        } catch(e: InterruptedException) {
            Thread.currentThread().interrupt(); save(); if(!run.get()) publish(false,"已暂停")
        } catch(e: Exception) {
            run.set(false); save(); publish(false,"训练异常：${e.javaClass.simpleName}: ${e.message}")
        }
    }
    private fun evaluate(weights: FloatArray): Float? {
        var sum=0L;var lastYield=System.nanoTime()
        // Never trains on these seeds. Identical test conditions for every candidate.
        for(seed in 0 until 16) {
            val g=SnakeEngine(seed=710000+seed); val p=SnakePolicy(g)
            while(!g.ended && g.steps<100000) { if(!alive()) return null; g.step(p.choose(weights).action)
                if(!fast && System.nanoTime()-lastYield>=32_000_000L) { Thread.sleep(32);lastYield=System.nanoTime() }
            }
            sum+=g.score
        }
        return sum/16f
    }
    private fun publish(active: Boolean,label: String,start: Long=0,startGames: Long=games,startSteps: Long=totalSteps) {
        val sec=if(start==0L) 0f else (System.nanoTime()-start)/1e9f
        stats=Stats(games,totalSteps,best,if(history.isEmpty()) 0f else history.sumOf { it.toLong() }.toFloat()/history.size,
            validation,championMean.coerceAtLeast(0f),updates,
            (0.12f/(1f+games/2000f)).coerceAtLeast(0.015f),active,history.toList(),deaths.toList(),
            if(sec>0) (games-startGames)*60f/sec else 0f,
            if(sec>0) (totalSteps-startSteps)/sec else 0f,
            if(saveError.isEmpty()) label else "$label · $saveError",evaluations,actor,learner.toList())
    }
    private fun save() {
        try {
            file.parentFile?.mkdirs()
            val payload=ByteArrayOutputStream()
            DataOutputStream(payload).use { o ->
                o.writeInt(3); o.writeLong(games); o.writeLong(totalSteps); o.writeLong(updates); o.writeInt(best)
                o.writeFloat(championMean); o.writeFloat(validation); o.writeLong(evaluations)
                learner.forEach { o.writeFloat(it) }; champion.forEach { o.writeFloat(it) }
                deaths.forEach { o.writeLong(it) }; o.writeInt(history.size); history.forEach { o.writeInt(it) }
            }
            val bytes=payload.toByteArray(); val crc=CRC32().apply { update(bytes) }.value
            val temp=File(file.path+".tmp"); val backup=File(file.path+".bak")
            FileOutputStream(temp).use { fos ->
                val out=DataOutputStream(fos); out.writeInt(0x534E524C); out.writeInt(bytes.size)
                out.write(bytes); out.writeLong(crc); out.flush(); fos.fd.sync()
            }
            if(file.exists()) {
                if(backup.exists() && !backup.delete()) error("备份删除失败")
                if(!file.renameTo(backup)) error("备份失败")
            }
            if(!temp.renameTo(file)) { if(backup.exists()) backup.renameTo(file); error("模型替换失败") }
            saveError=""
        } catch(e: Exception) { saveError="存档失败：${e.message}" }
    }
    private fun load() {
        for(source in listOf(file,File(file.path+".bak"))) {
            if(!source.exists()) continue
            try {
                DataInputStream(BufferedInputStream(FileInputStream(source))).use { input ->
                    require(input.readInt()==0x534E524C); val size=input.readInt(); require(size in 1..65536)
                    val bytes=ByteArray(size); input.readFully(bytes)
                    require(input.readLong()==CRC32().apply { update(bytes) }.value)
                    DataInputStream(ByteArrayInputStream(bytes)).use { o ->
                        require(o.readInt()==3)
                        val gs=o.readLong(); val st=o.readLong(); val up=o.readLong(); val bs=o.readInt()
                        val cm=o.readFloat(); val va=o.readFloat(); val ev=o.readLong()
                        val l=FloatArray(SnakePolicy.FEATURES) { o.readFloat() }
                        val c=FloatArray(SnakePolicy.FEATURES) { o.readFloat() }
                        val d=LongArray(4) { o.readLong() }; val count=o.readInt(); require(count in 0..120)
                        val h=IntArray(count) { o.readInt() }
                        require(l.all { it.isFinite() && abs(it)<=16 } && c.all { it.isFinite() && abs(it)<=16 })
                        require(gs>=0 && st>=0 && up>=0 && bs>=0 && cm.isFinite() && va.isFinite())
                        games=gs; totalSteps=st; updates=up; best=bs; championMean=cm; validation=va; evaluations=ev
                        learner=l; champion=c; d.copyInto(deaths); history.clear(); h.forEach { history.addLast(it) }
                    }
                }
                publish(false,if(source==file) "已加载模型" else "已恢复备份模型"); return
            } catch(_: Exception) { saveError="模型损坏，尝试备份" }
        }
        publish(false,if(saveError.isEmpty()) "新模型" else "模型无法恢复，已创建新模型")
    }
    companion object {
        @Volatile private var sharedInstance:SnakeTrainer?=null
        @Synchronized fun shared(file:File):SnakeTrainer {
            val existing=sharedInstance
            if(existing!=null && !existing.closed) return existing
            return SnakeTrainer(file).also { sharedInstance=it }
        }
    }
    @Synchronized override fun close() {
        if(closed) return
        closed=true; run.set(false);session.incrementAndGet()
        executor.submit { save(); publish(false,"已停止") }
        executor.shutdown() // Queued save finishes; never wait on Android's UI thread.
    }
}
