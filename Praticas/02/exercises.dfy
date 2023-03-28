
datatype List<T> = Nil | Cons( T, List<T> )

function length<T>( l: List<T> ) : nat
  decreases l
{
  match l
    case Nil => 0
    case Cons(_, r) => 1 + length( r )
}

lemma {:induction false} length_non_neg<T> ( l: List<T> )
  ensures length(l) >= 0
{
  match l
  //case Nil => assert true;
  case Nil => assert 0 >= 0;
  case Cons(_, r) =>
    length_non_neg( r );
    assert length( r ) >= 0;
    assert forall k: int :: k >= 0 ==> 1 + k>= 0; //

    assert 1 + length( r ) >= 0;
    assert 1 + length( r ) == length( l );
}

function lengthTL<T> (l: List<T>, acc: nat): nat
  {
    match l
      case Nil => acc
      case Cons(_, r) => lengthTL( r, 1 + acc )
}

// stronger induction hypothesis
lemma lengthTL_aux<T>(l: List<T>, acc: nat)
  ensures lengthTL(l, acc) == acc + length( l )
{
  match l
    case Nil => assert acc + length<T>(Nil) == acc;
    // apply the lemma it self with acc + 1
    case Cons(_, r) => lengthTL_aux(r, acc + 1);
}

lemma lengthEq<T>(l: List<T>)
  ensures length(l) == lengthTL(l, 0)
{
  lengthTL_aux(l, 0);

}


function square( n: int ): int { n * n }

method Q( n: nat ) returns ( r: int )
  ensures n >= r >= 0
  ensures square( r ) <= n < square( r + 1 )
{
   var count := 0;
   var sum   := 1;

   while( sum <= n )
    invariant 0 <= count
    invariant square( count ) <= n
    invariant sum == square( count + 1 );
   {
      count := count + 1;
      sum   := sum + 2 * count + 1;
   }

   return count;
}

method count( n:nat  ) returns ( s: int )
  ensures s == n
{
  var i := 0;
  while( i < n )
    invariant 0 <= i <= n
    invariant i <= n;
  {
    i := i + 1;
  }

  return i;
}

function sum'( n: nat ): nat
{
  if n == 0 then 0
  else n + sum'( n - 1 )
}

method sum( n: nat ) returns ( res: nat )
  ensures res == sum'( n )
{
  var i := 0;
  var s := 0;

  while ( i < n )
    invariant 0 <= i <= n
    invariant s == sum'( i );
  {
    i := i + 1;
    s := s + i;
  }

  return s;
}

method IntervalContains( lowA: nat, highA: nat, lowB: nat, highB: nat ) returns (res: bool)
  requires lowA <= highA
  requires lowB <= highB
  ensures lowA <= lowB && highA >= highB ==> true
{
  if ( lowA <= lowB && highA >= highB )
  {
    return true;
  }
  else
  {
    return false;
  }
}

method Main()
{
  var c := 17;


  var res := Q(c);

}
