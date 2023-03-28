/*
    method m(x_1, ..., x_n) returns (r)
    requires Pre(x_1, ..., x_n )   in Program
    ensures Post(x_1, ..., x_n )      Statements
*/


method Abs( x: int ) returns ( y: int )
  requires true
  ensures x < 0 ==> y == -x && x >= 0 ==> y == x
{
  if ( x < 0 ) {  return -x; }
  else         {  return  x; }
}

function f_max(x: int, y: int): int
{
  if x > y then x
  else          y
}

method Max2_func(x: int, y: int) returns (r: int)
  requires true
  ensures f_max(x, y) == r

{

}

method Max2(x: int, y: int) returns (r: int)
  ensures r >= x && r >= y
  ensures r == x || r == y
  {
    if ( x >= y ) { r := x; }
    else         { r := y; }
  }

method m1(x: int, y: int) returns (z:int)
  requires 0 < x < y
  ensures z >= 0 && z < y && z != x
{
  // assume 0 < x < y

  z := 0;
}


method m2(x: nat) returns (y: int)
  // pre condition is false and thus every body will
  // be true
  requires x <= -1
  ensures y > x && y < x
{

}

method Test()
{
  var result := Max2(42, 73);
  assert result == 73;
}
