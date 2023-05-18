datatype color = Yellow | Green | Red

class Semaforo
{
  var c : color;

  constructor( x: color)
    ensures match x
            case Yellow => IsYellow()
            case Green => IsGreen()
            case Red => IsRed()
  {
    this.c := x;
  }

  predicate IsGreen()
    reads `c
  {
     c == Green
  }

  predicate IsYellow()
    reads `c
  {
     c == Yellow
  }

  predicate IsRed()
    reads `c
  {
     c == Red
  }

  method turnRed()
    requires IsYellow()
    modifies `c
    ensures IsRed()
  {
    c := Red;
  }

  method turnGreen()
    requires IsRed()
    modifies `c
    ensures IsGreen()
  {
    c := Green;
  }

  method turnYellow()
    requires IsGreen()
    modifies `c
    ensures IsYellow()
  {
    c := Yellow;
  }
}

method Main()
{
  var s := new Semaforo( Green );

  s.turnYellow();
}
