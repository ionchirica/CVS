/*@
  fixpoint int sum(list<int> xs)
  {
    switch( xs )
    {
      case nil : return 0;
      case cons(h, t): return h + sum( t );
    }
  }
 @*/

/*@
 lemma_auto void sum_append(list<int> xs, list<int> ys)
 requires true;
 ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
 {
    switch( xs )
    {
      case nil:
      case cons(h, t): sum_append(t, ys);
      assert sum(append(xs, ys)) == sum(append(t, ys)) + h;
    }
 }
 @*/
public class Arrays
{

  public static int probe(int[] a, int i)
    //@ requires array_slice(a, 0, a.length, ?vs) &*& 0 <= i &*& i < a.length;
    //@ ensures array_slice(a, 0, a.length, vs) &*& result == nth( i, vs );
  {
    return a[i];
  }

  public static void update(int[] a, int i, int v)
    //@ requires array_slice(a, 0, a.length, ?vs) &*& 0 <= i &*& i < a.length;
    //@ ensures array_slice(a, 0, a.length, update(i, v, vs));
  {
    a[i] = v;
  }


  public static int sum(int[] a)
    // we gave ownership to the method
    //@ requires array_slice(a, 0, a.length, ?array);
    // we must also recover the ownership
    //@ ensures array_slice(a, 0, a.length, array) &*& result == sum(array);
    {
      int i = 0, total = 0;
      // give ownership to the while loop aswell
      while(i < a.length)
      //@ invariant 0 <= i &*& i <= a.length &*& array_slice(a, 0, a.length, array) &*& total == sum(take(i, array));
      {
        total += a[i];
        //@ take_one_more(i, array);
        //@ sum_append(take(i, array), cons(a[i], nil));
        i++;
      }
      return total;
    }


}
