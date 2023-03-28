
method max(a: array<int>, N:int) returns (M:int)
  requires 0 < N <= a.Length
{
  var m: int := a[0];
  var i: int := 0;

  while i < N{
    if a[i] >= m { m := a[i]; }
      i := i + 1;
  }


  return m;
}

function fact( n: nat ) : nat
  decreases n
{
  if n == 0 then 1
  else n * fact(n - 1)
}

function fact_acc( n: nat, a: int ): int
  decreases n
{
  if n == 0 then a
  else fact_acc( n - 1, n * a )
}

function fact_alt( n: nat ): int
{
  fact_acc( n, 1 )
}

lemma fact_acc_correct(n: nat, a: int)
  ensures fact_acc(n, a) == a * fact(n)
{
}

lemma fact_alt_correct (n: nat)
  ensures fact_alt(n) == fact(n)
{
  fact_acc_correct(n, 1); // lemmas end up with a semi-colon

  assert fact_acc(n , 1) == 1 * fact(n);
  assert 1 * fact(n) == fact(n);
  assert fact_alt(n) == fact_acc(n, 1);
}
