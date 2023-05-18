/*@ predicate SwapInv(Swap s; int v1, int v2 ) =
  s.x1 |-> v1 &*& s.x2 |-> v2;
  @*/


public class Swap
{
  int x1;
  int x2;

  public Swap()
  //@ requires true;
  //@ ensures x1 |-> 0 &*& x2 |-> 0;
    {
      x1 = 0;
      x2 = 0;
    }

  public void putZero()
  //@ requires SwapInv(this, ?v1, ?v2) &*& v1 >= 0;
  //@ ensures SwapInv(this, ?vv, v2) &*& vv <= 0;
    {
      x1 = -1;
    }

  public void poorSwap()
  //@ requires SwapInv(this, ?v1, ?v2);
  //@ ensures SwapInv(this, v2, v2 );
    {
      x1 = x2;
    }

  public void swap()
  //@ requires SwapInv(this, ?v1, ?v2 );
  //@ ensures SwapInv(this, v2, v1 );
    {
      int tmp = x1;
      x1 = x2;
      x2 = tmp;
    }

  public void transfer()
  //@ requires SwapInv(this, ?v1, ?v2) &*& v1 >= 0 ;
  //@ ensures SwapInv(this, 0, v1 + v2);
    {
      if( x1 > 0 )
      {
        x1--;
        x2++;
        transfer();
      }
    }

  public static void main()
  //@ requires true;
  //@ ensures true;
    {
      Swap s = new Swap();

      s.putZero();

    }
}
