
function power(n: int, m:nat): int
  decreases m
{
  if m == 0 then 1
  else n * power(n, m - 1)
}

function pow(n: int, m: nat, r: int): int
  decreases m
{
  if m == 0 then r
  else pow(n, m - 1, r * n)
}

function power_alt(n: int, m: nat) : int
{
  pow(n, m, 1)
}

lemma power_alt_correct(n: int, m: nat, a: int)
  ensures pow(n, m, a) == a * power(n, m)
  {}

lemma powerEquiv(n: int, m: nat)
  ensures power(n, m) == power_alt(n, m)
{
  power_alt_correct(n, m, 1);
}
