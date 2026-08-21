import re, sys

B = {
 '0_Tuple':'Unit', '2_Tuple':'Pair', 'Account':'Account', 'AccountList':'AccountList',
 'Bool':'bool', 'Box':'Box', 'Global':'Global', 'Int_i32':'i32', 'Int_isize':'isize',
 'Never':'Never', 'Param':'Param', 'Ref_immutable':'RefImm', 'Ref_mutable':'RefMut',
 'sum_balances_Closure_0':'Closure_sum_balances', 'sum_up_to_Closure_0':'Closure_sum_up_to',
 'Transaction':'Transaction',
}
BASES = sorted(B, key=len, reverse=True)

BINOP = {
 'mir_binop_Lt_Int_i32_Int_i32':'lt_i32_i32',
 'mir_binop_Le_Int_i32_Int_i32':'le_i32_i32',
 'mir_binop_AddWithOverflow_Int_i32_Int_i32':'add_ovf_i32_i32',
 'mir_binop_SubWithOverflow_Int_i32_Int_i32':'sub_ovf_i32_i32',
}
METHODS = {'m_account_deposit','m_account_over_limit','m_account_classify',
           'm_account_adjust','m_account_apply','m_sum_up_to','m_sum_balances'}

unmapped = set()

def base_of(rest):
    for b in BASES:
        if rest == b or rest.startswith(b + '_'):
            return b, rest[len(b):]
    return None, None

def rw(tok):
    if tok in BINOP: return BINOP[tok]
    if tok in METHODS: return tok[2:]
    if tok.startswith('iss_'): return 'is' + rw(tok[2:])
    for pre in ('make_generic_s_','make_concrete_s_'):
        if tok.startswith(pre):
            rest = tok[len(pre):]
            if rest in B: return ('generic_' if 'generic' in pre else 'concrete_') + B[rest]
            unmapped.add(tok); return tok
    for pre in ('make_generic_','make_concrete_'):
        if tok.startswith(pre):
            rest = tok[len(pre):]
            if rest in B: return pre + B[rest]
            unmapped.add(tok); return tok
    if tok.startswith('s_'):
        b, suf = base_of(tok[2:])
        if b is None: unmapped.add(tok); return tok
        return B[b] + suf
    if tok.startswith('p_'):
        b, suf = base_of(tok[2:])
        if b is None: unmapped.add(tok); return tok
        n = B[b]
        if suf == '': return 'own_' + n
        if suf == '_val': return 'val_' + n
        if suf == '_snap': return 'snap_' + n
        if suf == '_assign': return 'assign_' + n
        if suf == '_field_discr': return n + '_field_discr'
        if suf == '_arbitrary_value': return 'arbitrary_' + n
        m = re.fullmatch(r'_(\d+)_owned', suf)
        if m: return 'own_' + n + '_' + m.group(1)
        unmapped.add(tok); return tok
    if tok.startswith('mir_binop_') or tok.startswith('m_'):
        unmapped.add(tok)
    return tok

TOK = re.compile(r'[A-Za-z_][A-Za-z0-9_$]*')
for path in sys.argv[1:]:
    src = open(path).read()
    out = TOK.sub(lambda m: rw(m.group(0)), src)
    if out != src: open(path,'w').write(out)
if unmapped:
    print('UNMAPPED:', *sorted(unmapped), sep='\n  ')
