/*@ predicate CellInv(Cell c, int v) =
      c != null &*& c.data |-> v;
  @*/

class Cell
{
  public int data;
  public Cell(int data)
  //@ requires true;
  //@ ensures CellInv(this, data);
  {
    this.data = data;
  }

  public Cell clone()
  //@ requires CellInv(this, ?data);
  //@ ensures CellInv(result, data);
  {
    return new Cell(data);
  }
}

/*@ predicate CounterInv(Counter c, int v) =
      c != null &*& c.inc |-> ?inc &*& c.dec |-> ?dec &*&
      inc != null &*& dec != null &*&
      CellInv(inc, v) &*& CellInv(dec, v);
  @*/

public class Counter
{

  Cell inc, dec;

  public Counter()
  //@ requires true;
  //@ ensures CounterInv(this, 0);
  {
    inc = new Cell(0);
    dec = new Cell(0);
  }

  public void inc()
  //@ requires CounterInv(this, ?v);
  //@ ensures CounterInv(this, v + 1);
  {
    inc.data++;
  }

  public void dec()
  //@ requires CounterInv(this, ?v);
  //@ ensures CounterInv(this, v - 1);
  {
    dec.data++;
  }

  public Counter swap()
  //@ requires CounterInv(this, ?v);
  //@ ensures CounterInv(this, v) &*& CounterInv(this, -v);
  {
    Counter c = new Counter();

    c.inc = this.dec.clone();
    c.dec = this.inc.clone();

    //@ close CounterInv(c, v);
    //@ close CounterInv(c, -v);

    return c;

  }


}
