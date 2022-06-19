from lark import Lark

parser = Lark.open("MLTL.lark", rel_to=__file__, start="program")

def main():
  print(parser.parse("SPEC ♢[0]prop;"))

if __name__ == "__main__":
  main()