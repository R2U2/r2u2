

def gen_var(n: int) -> str:
    s: str = 'VAR\n'
    for i in range(0,n-1):
        s += 'a'+str(i)+','
    s += 'a'+str(n-1)+': bool;\n'

    s += 'Order: '
    for i in range(0,n-1):
        s += 'a'+str(i)+','
    s += 'a'+str(n-1)+';\n'

    return s


def gen_spec(n: int) -> str:
    s: str = 'SPEC\n'
    s += 'G[0,5]a0;'

    return s


if __name__ == '__main__':
    print(gen_var(5)+gen_spec(1))