from lark import Lark

parser = Lark.open("MLTL.lark", rel_to=__file__, start="program")

def main():
  print(parser.parse("SPEC label: ♢[0,5]prop*prop>prop+prop&&prop;").pretty())

if __name__ == "__main__":
  main()