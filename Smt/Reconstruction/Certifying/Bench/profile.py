#!/usr/bin/python3

import os
from sys import argv

def parseBinder(cmd: str) -> tuple[str, str]:
  cmdWords = cmd.split()
  binderName = cmdWords[1]
  assignOpIdx = cmdWords.index(":=")
  # we're using this function both on tactics and theorems
  # if cmd is a tactic we should use + 2
  # otherwise is + 1
  tactic = cmdWords[assignOpIdx + 1]
  if tactic == "by":
    tactic = cmdWords[assignOpIdx + 2]
  return (tactic, binderName)

def updateReport(fileName: str) -> str:
  outName = argv[1] + ".updated"
  with open(fileName) as leanScript:
    firstReportTime = True
    previousLine = ""
    out = open(outName, "w")
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
  return outName

def main():
  # scriptDir = os.path.dirname(__file__)
  # print("scriptDir =", scriptDir)
  leanFile = argv[1]
  outLean = updateReport(leanFile)
  profileOutput = os.popen("lean " + outLean).read()
  print(profileOutput)


if __name__ == '__main__':
  main()
