/*
 * Implement a savings account.
 * A savings account is actually made up of two balances.
 *
 * One is the checking balance, here account owner can deposit and withdraw
 * money at will. There is only one restriction on withdrawing. In a regular
 * bank account, the account owner can make withdrawals as long as he has the
 * balance for it, i.e., the user cannot withdraw more money than the user has.
 * In a savings account, the checking balance can go negative as long as it does
 * not surpass half of what is saved in the savings balance. Consider the
 * following example:
 *
 * Savings = 10
 * Checking = 0
 * Operation 1: withdraw 10 This operation is not valid. Given that the
 * the user only has $$10, his checking account
 * can only decrease down to $$-5 (10/2).
 *
 * Operation 2: withdraw 2 Despite the fact that the checking balance of
 * the user is zero,
 * money in his savings account, therefore, this
 * operation is valid, and the result would be
 * something like:
 * Savings = 10;
 * Checking = -2
 *
 * Regarding depositing money in the savings balance (save), this operation has
 * one small restrictions. It is only possible to save money to the savings
 * balance when the user is not in debt; i.e. to save money into savings, the
 * checking must be non-negative.
 *
 * Given the states:
 * STATE 1 STATE 2
 * Savings = 10 Savings = 10
 * Checking = -5 Checking = 0
 *
 * and the operation save($$60000000000), the operation is valid when executed
 * in STATE 2 but not in STATE 1.
 *
 * Finally, when withdrawing from the savings balance, an operation we will
 * call rescue, the amount the user can withdraw depends on the negativity of
 * the user’s checking account. For instance:
 * Savings: 12
 * Checking: -5
 *
 * In the case, the user could withdraw at most two int dollars ($$). If the
 * user withdrew more than that, the balance of the checking account would
 * go beyond the -50% of the savings account; big no no.
 */

public class Savings
{
  private int checking;
  private int savings;

  public Savings(int _checking, int _savings)
  //@ requires true;
  //@ ensures checking |-> _checking &*& savings |-> _savings;
    {
      this.checking = _checking;
      this.savings = _savings;
    }

  public int getChecking()
    //@ requires checking |-> ?v1;
    //@ ensures result == v1 &*& checking |-> v1;
    {
      return checking;
    }

  public int getSavings()
    //@ requires savings |-> ?v1;
    //@ ensures result == v1 &*& savings |-> v1;
    {
      return savings;
    }

  public void deposit(int amount)
    //@ requires checking |-> ?v1 &*& savings |-> ?v2 &*& amount >= 0 &*& v1 >= 0;
    //@ ensures checking |-> v1 &*& savings |-> v2 + amount;
    {
      if (checking >= 0)
        savings += amount;
    }

  public void withdraw(int amount)
    //@ requires checking |-> ?v1 &*& savings |-> ?v2 &*& amount >= 0 &*& v1 >= 0;
    //@ ensures checking |-> v1 - amount &*& savings |-> v2;
    {
      if (checking >= 0 && checking - amount >= -savings / 2)
        checking -= amount;
    }

  public void rescue(int amount)
    //@ requires checking |-> ?v1 &*& amount >= 0 &*& v1 < 0;
    //@ ensures checking |-> v1 + amount;
    {
      if (checking < 0)
        checking += amount;
    }
}
