import clipboard

with open(r"zz_makeProgram\cool.py", "r") as file:
  bigContents = file.read().split("\n")

with open("getGood.txt", "r") as file:
  bigContents[1] = 'r"""' + file.read() + '"""'


clipboard.copy("\n".join(bigContents))
print("********************************\nDONE\nDONE\nDONE\n********************************")