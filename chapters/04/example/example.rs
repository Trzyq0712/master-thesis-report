use prusti_contracts::*;

pub struct Account {
    pub balance: i32,
    pub limit: i32,
}

pub enum Transaction {
    Deposit(i32),
    Withdrawal(i32),
}

pub enum AccountList {
    Empty,
    Cons(Account, Box<AccountList>),
}

pub fn account_deposit(a: &mut Account, amount: i32) {
    if 0 < amount {
        a.balance = a.balance + amount;
    }
}

pub fn account_over_limit(a: &Account) -> bool {
    a.limit < a.balance
}

pub fn account_classify(a: &Account) -> i32 {
    if a.balance < a.limit {
        if 0 <= a.balance {
            0
        } else {
            -1
        }
    } else {
        1
    }
}

pub fn account_adjust(a: &mut Account, amount: i32) {
    if amount < 0 {
        a.balance = a.balance + amount;
    }
    if a.balance < 0 {
        a.balance = 0;
    }
}

pub fn sum_up_to(n: i32) -> i32 {
    let mut i = 0;
    let mut total = 0;
    while i < n {
        body_invariant!(true);
        total = total + i;
        i = i + 1;
    }
    total
}

pub fn account_apply(a: &mut Account, t: &Transaction) {
    match t {
        Transaction::Deposit(amount) => {
            a.balance = a.balance + *amount;
        }
        Transaction::Withdrawal(amount) => {
            a.balance = a.balance - *amount;
        }
    }
}

pub fn sum_balances(list: &AccountList) -> i32 {
    let mut total = 0;
    let mut cur = list;
    while let AccountList::Cons(a, rest) = cur {
        body_invariant!(true);
        total = total + a.balance;
        cur = rest;
    }
    total
}
