import clipboard

with open(r"zz_makeProgram\cool.py", "r") as file:
  bigContents = file.read().split("\n")

with open(r"zz_makeProgram\getGood.txt", "r") as file:
  bigContents[1] = 'r"""' + file.read() + '"""'

with open(r"zz_makeProgram\z_big-pyth.txt", "r") as file:
  bigContents[5] = file.read()


clipboard.copy("\n".join(bigContents))
print("********************************\nDONE\n********************************")