#!/usr/bin/python3

from sys import argv

def isStep(cmd: str) -> bool:
  cmdWords = cmd.split()
  if cmdWords:
    return cmdWords[0] == 'let' or cmdWords[0] == 'have'
  else:
    return False

def insertReport(fileName: str) -> str:
  outName = argv[1] + ".inserted"
  with open(fileName) as leanScript:
    firstStep = True
    out = open(outName, "w")
    for line in leanScript:
      if isStep(line):
        if firstStep:
          out.write("reportTime\n")
          firstStep = False
        out.write(line)
        out.write("reportTime\n")
      else:
        out.write(line)
  return outName

def main():
  insertReport(argv[1])

if __name__ == '__main__':
  main()
