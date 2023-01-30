#!/usr/bin/python3

from sys import argv

def parseBinder(cmd: str) -> tuple[str, str]:
  cmdWords = cmd.split()
  binderName = cmdWords[1]
  byIdx = cmdWords.index("by")
  tactic = cmdWords[byIdx + 1]
  return (tactic, binderName)

def main():
  with open(argv[1]) as leanScript:
    firstReportTime = True
    previousLine = ""
    out = open(argv[1] + ".updated", "w")
    for line in leanScript:
      outLine = ""
      if "reportTime" in line:
        if not firstReportTime:
          tactic, binderName = parseBinder(previousLine)
          outLine = f"reportTimeOfTactic {tactic}, {binderName}\n"
        else:
          firstReportTime = False
          outLine = "reportTime\n"
      else:
        outLine = line
      out.write(outLine)
      previousLine = line
    out.close()

if __name__ == '__main__':
  main()
