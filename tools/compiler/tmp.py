
class A:
  def __init__(self) -> None:
    print('A')

class B(A):
  def __init__(self,a) -> None:
    print('B '+str(a))
    super().__init__(a)  

class C(A):
  def __init__(self,a) -> None:
    # print('C '+str(a)+' '+str(b))
    print('C '+str(a))
    super().__init__()  

class D(B,C):
  def __init__(self,a,b,c) -> None:
    print('D')
    super().__init__(a)

if __name__ == '__main__':
  D(0,1,2)