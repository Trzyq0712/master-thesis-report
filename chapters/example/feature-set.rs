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
        total = total + a.balance;
        cur = rest;
    }
    total
}
