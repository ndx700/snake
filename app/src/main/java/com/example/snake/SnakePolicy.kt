package com.example.snake

import kotlin.math.abs
import kotlin.math.max
import kotlin.random.Random

/** Safe route planning plus a genuinely learned action-value residual.
 * One instance per engine/thread; scratch arrays are never shared between workers.
 */
class SnakePolicy(private val g: SnakeEngine) {
    data class Choice(val action: Int, val features: FloatArray, val reason: String,
        val region: Int, val tailSafe: Boolean, val predicted: Float)
    private val n = g.capacity
    private val blocked = BooleanArray(n)
    private val seen = BooleanArray(n)
    private val queue = IntArray(n)
    private val parent = IntArray(n)
    private val sim = IntArray(n)
    private val visits = IntArray(n)
    private var searchOrder = intArrayOf(0,1,2,3)
    private var lastSteps = -1
    var nodes = 0L; private set
    var choices = 0L; private set
    private fun prepare() { g.occupied.copyInto(blocked) }
    private fun path(start: Int, target: Int): IntArray? {
        if (target < 0) return null
        seen.fill(false); parent.fill(-1); var read=0; var write=0
        queue[write++] = start; seen[start]=true
        while(read < write) {
            val c=queue[read++]; nodes++
            if(c == target) {
                var count=0; var p=c
                while(p != start) { count++; p=parent[p] }
                val result=IntArray(count); p=c
                for(i in count-1 downTo 0) { result[i]=p; p=parent[p] }
                return result
            }
            for(a in searchOrder) { val v=g.next(c,a)
                if(v >= 0 && !seen[v] && !blocked[v]) { seen[v]=true; parent[v]=c; queue[write++]=v }
            }
        }
        return null
    }
    private fun region(start: Int): Int {
        seen.fill(false); var read=0; var write=1; queue[0]=start; seen[start]=true
        while(read < write) { val c=queue[read++]; nodes++
            for(a in searchOrder) { val v=g.next(c,a)
                if(v>=0 && !seen[v] && !blocked[v]) { seen[v]=true; queue[write++]=v }
            }
        }
        return write
    }
    private fun safeFoodPath(): IntArray? {
        prepare(); blocked[g.tail]=false
        val route=path(g.head,g.food) ?: return null
        if(route.isEmpty()) return null
        var len=g.length; for(i in 0 until len) sim[i]=g.cellAt(i)
        prepare(); var heading=g.direction
        for(c in route) {
            val a=(0..3).firstOrNull { g.next(sim[0],it)==c } ?: return null
            if(len>1 && a==(heading+2)%4) return null
            val eat=c==g.food
            if(blocked[c] && !(c==sim[len-1] && !eat)) return null
            if(!eat) blocked[sim[len-1]]=false
            if(eat) len++
            for(i in len-1 downTo 1) sim[i]=sim[i-1]
            sim[0]=c; blocked[c]=true; heading=a
        }
        if(len==n) return route
        blocked[sim[len-1]]=false
        // Reachability is a heuristic, not a proof; full route itself is checked with moving body.
        return if(path(sim[0],sim[len-1]) != null) route else null
    }
    /** Expand the tail path through free cells to open space instead of orbiting a small loop. */
    private fun longTailMove(): Int {
        prepare(); blocked[g.tail]=false
        if(g.food>=0) blocked[g.food]=true
        val short=path(g.head,g.tail) ?: return -1
        if(short.isEmpty()) return -1
        val route=ArrayList<Int>(n);route.add(g.head);short.forEach { route.add(it) }
        val used=blocked.copyOf();route.forEach { used[it]=true }
        var changed=true
        while(changed) {
            changed=false;var i=0
            while(i<route.size-1) {
                val u=route[i];val v=route[i+1]
                val horizontal=u/g.cols==v/g.cols
                val sides=if(horizontal) intArrayOf(0,2) else intArrayOf(1,3)
                for(a in sides) {
                    val x=g.next(u,a);val y=g.next(v,a)
                    if(x>=0 && y>=0 && !used[x] && !used[y]) {
                        route.add(i+1,x);route.add(i+2,y);used[x]=true;used[y]=true;changed=true;break
                    }
                }
                i++
            }
        }
        return actionTo(route[1]).let { if(g.legal(it)) it else -1 }
    }
    private fun actionTo(cell: Int): Int = (0..3).first { g.next(g.head,it)==cell }
    fun choose(weights: FloatArray, epsilon: Float=0f, rng: Random=Random.Default): Choice {
        if(g.steps < lastSteps || g.steps==0) visits.fill(0)
        lastSteps=g.steps; visits[g.head]++; choices++
        searchOrder=(0..3).sortedByDescending { weights[12+it] }.toIntArray()
        val foodPath=safeFoodPath()
        val suggested=foodPath?.firstOrNull()?.let { actionTo(it) } ?: -1
        val tailMove=if(suggested<0) longTailMove() else -1
        val candidates=ArrayList<Choice>(4)
        for(a in 0..3) {
            if(!g.legal(a)) continue
            val h=g.next(g.head,a); val eat=h==g.food
            prepare(); if(!eat) blocked[g.tail]=false; blocked[h]=true
            val len=g.length+if(eat) 1 else 0
            val newTail=if(eat || g.length==1) if(g.length==1 && !eat) h else g.tail else g.cellAt(g.length-2)
            blocked[newTail]=false
            val r=region(h); val tail=path(h,newTail)!=null
            var mobility=0
            for(d in 0..3) { val v=g.next(h,d)
                if(d != (a+2)%4 && v>=0 && (!blocked[v] || v==newTail)) mobility++
            }
            val dist=if(eat) 0 else path(h,g.food)?.size ?: n
            val oldDist=abs(g.head%g.cols-g.food%g.cols)+abs(g.head/g.cols-g.food/g.cols)
            val newDist=if(eat) 0 else abs(h%g.cols-g.food%g.cols)+abs(h/g.cols-g.food/g.cols)
            val free=max(1,n-len+1)
            val f=floatArrayOf(1f, if(eat) 1f else 0f,
                (oldDist-newDist).toFloat()/2f, 1f-dist.toFloat()/n,
                r.toFloat()/free, if(tail) 1f else 0f, mobility/3f,
                len.toFloat()/n, g.hunger/500f,
                (visits[h].coerceAtMost(10)/10f),
                if(a==suggested) 1f else 0f,
                if(h%g.cols==0 || h%g.cols==g.cols-1 || h/g.cols==0 || h/g.cols==g.rows-1) 1f else 0f) + FloatArray(4) { if(it==a) 1f else 0f }
            val q=value(weights,f)
            candidates.add(Choice(a,f,if(a==suggested) "安全食物路线" else if(a==tailMove) "展开尾巴路线" else if(tail) "保留尾巴通路" else "空间逃生",r,tail,q))
        }
        if(candidates.isEmpty()) return Choice(g.direction,FloatArray(FEATURES),"无可行动作",0,false,0f)
        val safe=candidates.filter { it.action==suggested || it.tailSafe && (it.features[6]>0f || g.length==n-1 && it.features[1]>0f) }
        val pool=if(safe.isNotEmpty()) safe else candidates
        if(epsilon>0 && rng.nextFloat()<epsilon) return pool[rng.nextInt(pool.size)]
        // Residual cannot override an immediate collision, and has a bounded influence.
        return pool.maxByOrNull {
            val foodBonus=if(it.action==suggested) 8f else 0f
            val trappedPenalty=if(!it.tailSafe && it.action!=suggested && g.length<n-1) 8f else 0f
            val seek=if(suggested>=0) it.features[3]*2 else -it.features[3]*1.5f
            foodBonus + (if(it.action==tailMove) 6f else 0f) + it.features[4]*3f + it.features[6]*0.6f + seek -
                it.features[9]*2f - trappedPenalty + it.predicted.coerceIn(-4f,4f)*0.7f
        }!!
    }
    companion object {
        const val FEATURES=16
        fun value(weights: FloatArray,f: FloatArray): Float {
            var result=0f; for(i in 0 until FEATURES) result+=weights[i]*f[i]; return result
        }
    }
}
