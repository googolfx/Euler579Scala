import scala.math._
import scala.collection.mutable.ArraySeq

object Euler579Solve extends App {

  println("Initiating Solve...")
  
  var ans = 0
  val MOD = 2 * 10^9
  
  def gcd(a:Int*):Int = {
    var t = 0
    for(x <- a) {
      if( t==0 )
        t=x
      else {
         var y = x
         while(y!=0) {
           val o = y
           y = t % y
           t = o
         }
      }
    }
    t
  }
     
  def ¡î(x:Int):Int = {
    sqrt( x.toFloat + 0.9 ).toInt
  }
  
  def cmp(a:ArraySeq[Int], b:ArraySeq[Int]):Int = {
    if( a(0) != b(0) ) return b(0)-a(0)
    if( a(1) != b(1) ) return b(1)-a(1)
    if( a(2) != b(2) ) return b(2)-a(2)
    0
  }
  
  def nLattice(a:ArraySeq[Int], b:ArraySeq[Int], c:ArraySeq[Int], t:Int):Int = {
    val d1 = abs(gcd(a:_*))
    val d2 = abs(gcd(b:_*))
    val d3 = abs(gcd(c:_*))
    
    (t+1) * (t*t-t+1+d1+d2+d3)
  }
  
  def add(n:Int, _M:Matrix[Int], _t:Int):Unit = {
    if( !(cmp(_M(0).map(a => a * -1), _M(0)) > 0 && cmp(_M(0), _M(1)) > 0 && cmp(_M(1), _M(2)) > 0 ) ) return
    
    val g = gcd( _M(0,0), _M(0,1), _M(0,2), _M(1,0), _M(1,1), _M(1,2), _M(2,0), _M(2,1), _M(2,2) );
    val M = Matrix.unflatten(3, ArraySeq(_M(0,0)/g, _M(0,1)/g, _M(0,2)/g,
                                          _M(1,0)/g, _M(1,1)/g, _M(1,2)/g,
                                          _M(2,0)/g, _M(2,1)/g, _M(2,2)/g))
    val t = _t / g
    val y0 = abs(M(0,0)) + abs(M(1,0)) + abs(M(2,0));
    val y1 = abs(M(0,1)) + abs(M(1,1)) + abs(M(2,1));
    val y2 = abs(M(0,2)) + abs(M(1,2)) + abs(M(2,2));
    val max_scale = n / max(y0, max(y1, y2))
    
    if( max_scale > 0 ) {
      for(scale <- 1 to max_scale) {
//        (nLattice(M[0] * scale, M[1] * scale, M[2] * scale, t * scale) % MOD) % MOD
          val v = ((((n+1-y0*scale)*(n+1-y1*scale)*(n+1-y2*scale)) % MOD) * (nLattice( M(0).map(a => a * scale), M(1).map(a => a * scale), M(2).map(a => a * scale), t*scale) % MOD)) % MOD
          ans += v
      }
    }
    //ans += 0
  }
  
  def addTuple(n:Int, _case:Int, a:Int, b:Int, c:Int, d:Int):Unit = {
    if( gcd(a, b, c, d) != 1 ) return
    
    val M0 = a*a+b*b-c*c-d*d; val M1 = 2*(b*c+a*d); val M2 = 2*(b*d-c*a)
    val M3 = 2*(b*c-a*d); val M4 = a*a-b*b+c*c-d*d; val M5 = 2*(c*d+b*a)
    val M6 = 2*(b*d+c*a); val M7 = 2*(c*d-b*a); val M8 = a*a-b*b-c*c+d*d
    
    if( !( (0<=M0 && M0<=M3 && M3<=M6) || (0>=M0 && M0>=M3 && M3>=M6) ) ) return
    
    val M = Matrix.unflatten(3, ArraySeq(M0, M1, M2, M3, M4, M5, M6, M7, M8))
    
    val t = a*a + b*b + c*c + d*d
    if( t > 4*n ) return
    
    if(_case==0 && 0<=M(0,0) && M(0,0)<=M(1,0) && M(1,0)<=M(2,0))
      add(n, M, t)
    else if(_case==1 && 0>=M(0,0) && M(0,0)>=M(1,0) && M(1,0)>=M(2,0)) {
      val Inv = M * Matrix.unflatten(3, ArraySeq(-1,0,0,0,-1,0,0,0,-1))
      add(n, Inv, t)
    }
  }
  
  def gen(n:Int) = {

    for(_case <- 0.to(1))
      for(a <- -n to n if a*a <= 4*n; b <- -n to n if a*a+b*b <= 4*n; c <- -n to n if a*a+b*b+c*c <= 4*n) {
        
        val L0 = - ¡î(5*n - a*a - b*b - c*c)
        val R0 = ¡î(5*n - a*a - b*b - c*c)
        val L1 = max(L0, -n)
        val R1 = max(R0, n)
   
        val L2 = if((a+b>0 && _case==0) || (a+b<0 && _case==1)) max(L1, (b-a)*c/(a+b)-1) else L1
        val R2 = if((a+b>0 && _case==1) || (a+b<0 && _case==0)) min(R1, (b-a)*c/(a+b)+1) else R1
               
        val _t1 = 2*a*a + b*b - c*c - 2*b*c
        val _t2 = a*a + b*b - c*c
      
        if((_case==0 && _t2<0) || (_case==1 && _t1<0)) 0 else {
          
          val t1 = max(_t1, 0)
          val t2 = max(_t2, 0)
          
          val t = ¡î( if(_case==0) t2 else t1 ) + 1
          val L3 = max(L2, if(_case==0) -t else a-t)
          val R3 = max(R2, if(_case==0) t else a+t)
          val Lj = (if(_case==0) a else 0) - ¡î( if(_case==0) t1 else t2 ) + 1
          val Rj = (if(_case==0) a else 0) + ¡î( if(_case==0) t1 else t2 ) - 1
          
          for(d <- L3 to R3+1)
            addTuple(n, _case, a, b, c, d)
        }
      }
    
    ans
  }
  
  val n = 5
  val result = gen(n)
  println("Value of S("+n+")=" + result)
}