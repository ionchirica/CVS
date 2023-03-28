function fib( n: nat ): nat
{
  if( n == 0 ) then 1 else
  if( n == 1 ) then 1 else
  fib( n - 1 ) + fib ( n - 2 )
}

method Fib(n: nat) returns (r: nat)
  ensures r == fib( n )
{
  if( n == 0 )
  {
    return 1;
  }

  var next := 2;
  r := 1;

  var i := 1;

  while( i < n )
    invariant 1 <= i <= n
    invariant r == fib( i )
    invariant next == fib( i + 1 )
  {
    var tmp := next;
    next := next + r;
    r := tmp;
    i := i + 1;
  }

  assert r == fib( n );
}


datatype List<T> = Nil | Cons( head: T, tail: List<T> )

function add( l: List<int> ): int
{
  match l
    case Nil => 0
    case Cons(x, xs) => x + add(xs)
}

method addImp( l: List<int> ) returns ( r: int )
  ensures r == add(l)
{
  var ll := l;
  r := 0;
  while(ll != Nil)
    decreases ll
    invariant r == add( l ) - add( ll )
  {
    r := r + ll.head;

    ll := ll.tail;
  }

  assert r == add( l );
}

method maxArray( arr: array<int> ) returns (max: int)
  requires arr.Length > 0
  ensures forall k :: 0 <= k < arr.Length ==> max >= arr[k] // é o maior elemento
  ensures exists k :: 0 <= k < arr.Length && arr[k] == max // o elemento existe
{
  max := arr[0];
  var i := 1;

  while( i < arr.Length )
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> max >= arr[j] // é o maior elemento
    invariant exists j :: 0 <= j < i && arr[j] == max // o elemento existe
  {
    if( arr[i] >= max )
    {
      max := arr[i];
    }
    i := i + 1;
  }

  assert forall k :: 0 <= k < arr.Length ==> max >= arr[k];
}

method MaxArrayDesc( arr: array<int> ) returns (max : int)
  requires arr.Length > 0
  ensures forall j :: 0 <= j < arr.Length ==> max >= arr[j] // é o maior elemento
  ensures exists j :: 0 <= j < arr.Length && arr[j] == max // o elemento existe
{
  max := arr[arr.Length - 1];
  var i := arr.Length - 2;

  while( i >= 0 )
    invariant -1 <= i <= arr.Length - 1
    invariant forall j :: i < j < arr.Length ==> max >= arr[j] // é o maior elemento
    invariant exists j :: i < j < arr.Length && arr[j] == max // o elemento existe
  {
    if( arr[i] >= max )
    {
      max := arr[i];
    }
    i := i - 1;
  }
}

function sum(n: nat) : nat
{
  if n == 0
    then 0
  else
    n + sum(n - 1)
}

method sumBackwards(n : nat) returns ( r: nat )
  ensures r == sum(n)
{
  var n' := n;
  r := 0;
  while( n' >= 1 )
    invariant 0 <= n'
    invariant r == sum(n) - sum(n')
  {
    r := r + n';
    n' := n' - 1;
  }

  assert r == sum(n);
}

function sumLimits( a: array<int>, up: int, down: int ): int
  reads a
  requires 0 <= down <= up < a.Length
  decreases up
{
  if down >= up then a[up]
  else              a[up] + sumLimits( a, up - 1, down )
}

method sumAndMax( arr: array<int> ) returns (sum: int, max: int)
  requires arr.Length > 0
  ensures forall k :: 0 <= k < arr.Length ==> max >= arr[k]   // é o maior elemento
  ensures exists k :: 0 <= k < arr.Length && arr[k] == max   // o elemento existe
  ensures sum == sumLimits(arr, arr.Length - 1, 0 )
{
  max := arr[0];
  sum := arr[0];
  var i := 1;

  while( i < arr.Length )
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> max >= arr[j]    // é o maior elemento
    invariant exists j :: 0 <= j < i && arr[j] == max    // o elemento existe
    invariant sum == sumLimits( arr, i - 1, 0 )
  {
    if( arr[i] >= max )
    {
      max := arr[i];
    }
    sum := sum + arr[i];
    i := i + 1;
  }

  assert sum == sumLimits(arr, arr.Length - 1, 0 );
}

// return -1 if "e" is not in array
// return index if "e" is in array
method search<T(==)>( arr:array<T>, e: T ) returns ( ind: int )
  requires arr.Length > 0
  ensures 0 <= ind ==> ind < arr.Length && arr[ind] == e
  ensures ind < 0 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != e
{
  var ix := 0;

  while( ix < arr.Length )
    invariant 0 <= ix <= arr.Length
    invariant forall k :: 0 <= k < ix ==> arr[k] != e
  {
    if( arr[ix] == e )
    {
      return ix;
    }

    ix := ix + 1;
  }

  return -1;
}

