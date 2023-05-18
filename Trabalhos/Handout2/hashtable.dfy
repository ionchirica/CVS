/*----------------------------------------------------*
|                                                     |
|                 Verified Hashtable                  |
|                /                  \                 |
|               /                    \                |
|        Antonio Brejo           Ion Chirica          |
|            58152                  64475             |
|                                                     |
*----------------------------------------------------*/

/*-------------------------------------------------*
|                                                  |
|            List and Option definition            |
|                                                  |
*-------------------------------------------------*/
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Option<T> = None | Some(value: T)

/*-------------------------------------------------*
|                                                  |
|           Pure functions provided by             |
|              the handout statement               |
|                                                  |
*-------------------------------------------------*/
ghost function mem<T>(x: T, xs: List<T>): bool
{
  match xs{
    case Nil => false
    case Cons(y, ys) => x == y || mem(x, ys)
  }
}

ghost function length<T>(xs: List<T>): nat
{
  match xs{
    case Nil => 0
    case Cons(y, ys) => 1 + length(ys)
  }
}

function list_find<K(==), V(!new)>(k: K, l: List<(K, V)>): Option<V>
  ensures match list_find(k, l)
{
    case None => forall v :: !mem((k, v), l)
    case Some(v) => mem((k, v), l)
}
{
  match l{
    case Nil => None
    case Cons((k', v), l') => if k == k' then Some(v) else list_find(k, l')
  }
}

function list_remove<K(==, !new), V(!new)>(k: K, l:List<(K, V)>): List<(K,V)>
  decreases l
  ensures forall k', v :: mem((k', v), list_remove(k, l)) <==> (mem((k', v), l) && k != k')
  ensures length(list_remove(k, l)) <= length(l)

{
  match l{
    case Nil => Nil
    case Cons((k', v), l') =>
      if k == k' then list_remove(k, l')
    else Cons((k', v), list_remove(k, l'))
  }
}

/*--------------------------------------------------------*
|                                                         |
|                    Hashtable Class.                     |
|      We define a hashtable as an Array of Buckets.      |
|    In essence, Buckets are Lists that hold pairs (K,V)  |
|        where the keys have the same hash value.         |
|                                                         |
*--------------------------------------------------------*/
class Hashtable<K(==, !new), V(!new)>
{
  var size: int;
  var data: array<List<(K, V)>>;

  ghost var Repr: set<object>;
  ghost var elems: map<K, Option<V>>;

  /*--------------------------------------------------------*
  |                                                         |
  |                Representation Invariant:                |
  |• _this_ and _data_ are contained in the set Repr, where |
  |     we find class fields opaque to the client view.     |
  |   • every element of a bucket actually belongs there    |
  |   • our hashtable is faithful to a logical Map          |
  |                                                         |
  *--------------------------------------------------------*/
  ghost predicate RepInv()
    reads this, Repr
  {
    this in Repr && data in Repr && data.Length > 0
      && (forall i :: 0 <= i < data.Length ==> valid_hash(data, i))
      && (forall k, v :: valid_data(k, v, elems, data))
  }
  /*---------------------------------------------------------------*
  |                                                                |
  |          valid_hash(a: array<List<K,V>>, bucket: int)          |
  |                                                                |
  |     Predicate that is true when the hash of all the keys       |
  |          within _a[_bucket_]_ are equal to _bucket_.           |
  |                                                                |
  *---------------------------------------------------------------*/
  ghost predicate valid_hash<K(!new), V(!new)>(d: array<List<(K, V)>>, s: int)
    reads d, this
    requires 0 <= s < d.Length
  { forall k, v :: mem((k, v), d[s]) ==> (bucket(k, d.Length) == s) }

  /*-----------------------------------------------------------------*
  |                                                                  |
  |                         valid_data(...)                          |
  |                                                                  |
  |   Predicate that is true when all the Keys in the logical Map    |
  |  can also be found in the appropriate Bucket of the Hashtable.   |
  |                                                                  |
  |    Maintains faithfulness to a logical representation of Map.    |
  |                                                                  |
  *-----------------------------------------------------------------*/
  ghost predicate valid_data<K(!new), V(!new)>(k: K, v:V, m: map<K, Option<V>>, d: array<List<(K, V)>>)
    requires d.Length > 0
    reads d, this
  { k in m && m[k] == Some(v) <==> mem((k,v),d[bucket(k, d.Length)]) }

  /*----------------------------------------------------------------*
  |                                                                 |
  |                  Find(k: Key): Option<V>                        |
  |                                                                 |
  |       It looks for the Key _k_ in the appropriate bucket.       |
  | If _key_ is found in the bucket, it should be expected: Some(v) |
  | Otherwise it is expected:                               None    |
  |                                                                 |
  *----------------------------------------------------------------*/
  method find(k: K) returns (r: Option<V>)

    requires RepInv()
    ensures RepInv()

    ensures fresh(Repr - old(Repr))
    ensures match r
  {
    case None =>    k !in elems || (k in elems && elems[k] == None)
    case Some(v) => k in elems && elems[k] == Some(v)
  }
  {
    var bucket_index := bucket(k, data.Length);

    r := list_find( k, this.data[ bucket( k,  data.Length ) ] );

    assert forall k,v :: valid_data(k, v, elems, data) && (k in elems && elems[k] == Some(v) <==>  mem((k,v),data[bucket(k, data.Length)]));

    assert match r
    {
      case Some(v) => k in elems && elems[k] == Some(v)
      case None =>   forall v :: !mem((k, v), this.data[bucket(k, this.data.Length)]) &&
                          (k !in elems || (k in elems && elems[k] == None))
    };

  }

  function hash<K(==, !new)>(key: K): int

  function bucket<K(==, !new)>(k: K, n:int): int
    requires n > 0
    ensures 0 <= bucket(k, n) < n
  {
    hash(k) % n
  }

  /*-------------------------------------------------------------*
  |                                                              |
  |                    Constructor( n: int )                     |
  |                                                              |
  | Construct the Hashtable with an initial array of size _n_.   |
  |            All elements of the List are set to Nil.          |
  |       The number of elements in the table is set to 0.       |
  |                                                              |
  *--------------------------------------------------------------*/
  constructor(n: int)
    requires n > 0
    ensures RepInv() && fresh(Repr - {this})
  {
    this.size := 0;

    this.data := new List<(K, V)>[n] ( _ => Nil );
    new;

    Repr := {this, data};
    elems := map[];

    assert size == |elems| && size == 0;
  }

  /*---------------------------------------------------------------*
  |                                                                |
  |                            Clear()                             |
  |                                                                |
  |                     Clears the hashtable.                      |
  |            All elements of the List are set to Nil.            |
  |        The number of elements in the table is set to 0         |
  |                                                                |
  *----------------------------------------------------------------*/
  method clear()
    modifies Repr
    requires RepInv()
    ensures RepInv() && fresh( Repr - old(Repr) )
  {
    Repr := Repr - {data};

    forall i | 0 <= i < data.Length
    {
      data[ i ] := Nil;
    }

    Repr := Repr + {data};
    this.size := 0;

    elems := map[];
  }

  /*---------------------------------------------------------------*
  |                                                                |
  |                         Remove(k: Key)                         |
  |                                                                |
  |         Removes the pair (Key, Value) if found by _k_.         |
  |       It is guaranteed that after a call to this method,       |
  |           _k_ is no longer found in the hashtable.             |
  |                                                                |
  *----------------------------------------------------------------*/
  method remove(k: K)
    modifies Repr, `elems
    requires RepInv()
    ensures RepInv()

    ensures k !in elems || (k in elems && elems[k] == None)
    ensures fresh(Repr - old(Repr))
  {
    var bucket_index := bucket(k, data.Length);

    var find_k := list_find(k, this.data[bucket_index]);

    assert forall k', v' :: valid_data(k', v', elems, data) && (k' in elems && elems[k'] == Some(v') <==>  mem((k',v'),data[bucket(k', data.Length)]));
    match find_k{
      case None =>
        assert forall v :: !mem((k, v), this.data[bucket_index]);
        assert forall i :: 0 <= i < data.Length ==> (valid_hash(data, i));
        assert k !in elems || (k in elems && elems[k] == None);

      case Some(v) =>
        assert forall i:: 0 <= i < data.Length ==> (valid_hash(data, i)) && forall k, v :: mem((k, v), data[i]) ==> bucket(k, data.Length) == i;

        Repr := Repr - {data, this};
        data[bucket_index] := list_remove(k, this.data[bucket_index]);
        elems := elems - {k};
        Repr := Repr + {data, this};
        size := size - 1;
    }
  }

  /*-------------------------------------------------------------------*
  |                                                                    |
  |                       Add(k: Key, v: Value)                        |
  |                                                                    |
  |        A call to this method can mean both an insert or a          |
  |   change to an already existing key. An insert, formally, means    |
  |   that the Key wasn't present in the Hashtable before the call.    |
  |   And changing the value held by the key means removing the old    |
  |                pair and then appending the new one.                |
  |                                                                    |
  |Intuitively, we can call Remove(_k_) first and then perform the add.|
  |           As if the pair is not found, nothing is done.            |
  |                                                                    |
  |If an insertion can result in the Hashtable reaching its load factor|
  |           threshold, a Resize() operation is dispatched.           |
  |                                                                    |
  |   It is guaranteed that after a call to this method, we can find   |
  |                      (K, V) in the Hashtable.                      |
  |                                                                    |
  *-------------------------------------------------------------------*/
  method add(k: K, v: V)
    modifies this, Repr, `elems

    requires RepInv()
    ensures RepInv()

    ensures fresh(Repr - old(Repr))
    ensures k in elems && elems[k] == Some(v)
  {

    if ( size == data.Length * 3 / 4 )
    {
      resize();
    }

    remove(k);

    var bucket_index := bucket(k, data.Length);

    assert forall k', v' :: valid_data(k', v', elems, data) && (k' in elems && elems[k'] == Some(v') <==>  mem((k',v'),data[bucket(k', data.Length)]));
    assert forall i:: 0 <= i < data.Length ==> (valid_hash(data, i)) && forall k, v :: mem((k, v), data[i]) ==> bucket(k, data.Length) == i;

    Repr := Repr - {data, this};
    this.data[bucket_index] := Cons((k, v), this.data[bucket_index]);
    elems := elems[k := Some(v)];
    Repr := Repr + {data, this};

    this.size := this.size + 1;
  }

  /*---------------------------------------------------------------*
  |                                                                |
  |                          Rehash(...)                           |
  |                                                                |
  |       This method recursivelly rehashes a List [Bucket].       |
  |                                                                |
  | We call this method whenever we wish to resize the hashtable.  |
  |                   Opaque to the client view.                   |
  |                                                                |
  *----------------------------------------------------------------*
  |     This snippet was responsively provided by the teachers.    |
  *---------------------------------------------------------------*/
  method rehash(arr: array<List<(K,V)>>, l : List<(K,V)>, oldSize : int, newSize : int, index : int)
    requires RepInv()
    requires 0 < oldSize == data.Length
    requires arr.Length == newSize == (oldSize * 2)
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == index
    requires forall j :: 0 <= j < newSize ==> valid_hash(arr, j)
    requires forall k,v :: (
    if 0 <= bucket(k, oldSize) < index then valid_data(k,v,elems,arr)
    else if bucket(k, oldSize) == index then
        (k in elems && elems[k] == Some(v))
      <==> mem((k,v), l) || mem((k,v), arr[bucket(k, newSize)])
    else
      !mem((k,v), arr[bucket(k, newSize)]) )
      ensures RepInv()
      ensures forall j :: 0 <= j < newSize ==> valid_hash(arr, j)
      ensures forall k,v :: if 0 <= bucket(k, oldSize) <= index then valid_data(k,v,elems,arr)
    else
      !mem((k,v), arr[bucket(k, newSize)])
      modifies arr
      decreases l
  {
    match l
    {
    case Nil => return;
    case Cons((k,v), xs) =>
      {
        var bucket := bucket(k, newSize);
        arr[bucket] := Cons((k,v), arr[bucket]);
        rehash(arr, xs, oldSize, newSize, index);
      }
    }
  }

  /*---------------------------------------------------------------*
  |                                                                |
  |                            Resize()                            |
  |                                                                |
  |  A call to this method is expected to come from Add(), where   |
  |           the load factor of 0.75 has been reached.            |
  |                                                                |
  | The Hashtable has now double the capacity. We must rehash the  |
  |              old keys to the newly created table.              |
  |                                                                |
  *---------------------------------------------------------------*/
  method resize()
    modifies Repr
    requires RepInv()
    ensures RepInv()
    ensures fresh(Repr - old(Repr))
  {
    var oldSize := data.Length;
    var newSize := (oldSize * 2);
    var arr := new List<(K,V)>[newSize] ( _ => Nil );

    var index := 0;

    while(index < oldSize)
      modifies arr
      invariant Repr == old(Repr)
      invariant 0 <= index <= oldSize
      invariant oldSize == data.Length
      invariant arr.Length == newSize == (oldSize * 2)
      invariant old(data) == data
      invariant arr != data
      invariant forall j :: 0 <= j < arr.Length ==> valid_hash(arr, j)
      invariant forall j :: 0 <= j < index ==> valid_hash(arr, j)
      invariant forall k,v :: ( if    0 <= bucket(k, oldSize) < index then
                                valid_data(k,v,elems,arr)
                          else !mem((k,v), arr[bucket(k, newSize)]) )
    {
      var list := data[index];

      assert valid_hash(data, index) && forall k, v :: mem((k,v), data[index]) ==> bucket(k, data.Length) == index;
      assert forall k, v :: valid_data(k,v,elems,data) && ((k in elems && elems[k] == Some(v)) <==> mem((k,v), data[bucket(k, data.Length)]));
      assert forall k,v :: (
        if      0 <= bucket(k, data.Length) < index then
          valid_data(k,v,elems,arr)
        else if bucket(k, data.Length) == index    then
          (k in elems && elems[k] == Some(v)) <==> mem((k,v), data[index]) || mem((k,v), arr[bucket(k, arr.Length)])
        else !mem((k,v), arr[bucket(k, arr.Length)]) );

      rehash(arr, list, oldSize, newSize, index);

      index := index + 1;
    }

  assert forall i :: 0 <= i < arr.Length ==> valid_hash(arr, i);

  Repr := Repr - {data, this};
  data := arr;
  Repr := Repr + {data, this};

  assert forall i :: 0 <= i < data.Length ==> valid_hash(data, i);
  assert forall k, v :: valid_data(k, v, elems, data) ==> (k in elems && elems[k] == Some(v) <==> mem((k,v), data[bucket(k, newSize)]));
  }
}
