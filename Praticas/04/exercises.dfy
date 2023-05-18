function sum( arr: array<int>, down: int, up: int ) : int
    reads arr
    requires 0 <= down <= up <= arr.Length
    decreases up - down
  {
    if down >= up then 0
    else              arr[down] + sum( arr, down + 1, up )
  }


/* -------------------------------- 1 ---------------------------------- */

  method fillK( a: array<int>, n: int, k:int, c: int ) returns (b : bool)
    requires 0 <= c <= n < a.Length
    ensures b == true  ==> forall k' :: 0 <= k' < c <= n < a.Length ==> a[k'] == k
    ensures b == false ==> exists k' :: 0 <= k' < c <= n < a.Length  && a[k'] !=  k
  {
    var ix := 0;

    while( ix < c )
      invariant 0 <= ix <= c
      invariant forall k' :: 0 <= k' < ix ==> a[k'] == k
    {
      if( a[ix] != k )
      {
        return false;
      }

      ix := ix + 1;
    }

    return true;
  }

  method Test()
    {
      var bb := new int[3];
      bb[0] := 1;
      bb[1] := 2;
      bb[2] := 3;
      var agg := fillK ( bb, 0,0,  2 );

      assert agg == true;

  }
/* -------------------------------- 2 ---------------------------------- */

  method containsSubString( a:array<char>, b:array<char> ) returns (pos: int)

  {

  }

method b(a : array<int>) returns (b : bool)
  requires 0 < a.Length
  ensures b ==> a[0] == 0
{
  return a[0] == 0;
}

method a()
{
  var i := 0;
  var n := 0;

  while( i < 10 )
    invariant i == 0 && (n == 0 || n == 1)
  {
    n := (n + 1) % 2;
  }
}
