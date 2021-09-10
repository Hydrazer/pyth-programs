import sys

pythShrinker = {
  "println": "\n",
  "sep": " ",
  "no-print": " ",
  "not": "!",
  "str-start": '"',
  "str-end": '"',
  "implicit-str-end": "",
  "until-break": "#",
  "until-error": "#",
  "forever": "#",
  "func-filter": "#",
  "py-literal": "$",
  "mod": "%",
  "mod-slice": "%",
  "format": "%",
  "and": "&",
  "open-file": "'",
  "open-image": "'",
  "open-website": "'",
  "tuple": "(",
  "end-args": ")",
  "end-block": ")",
  "times": "*",
  "repeat": "*",
  "cartesian-product": "*",
  "plus": "+",
  "concat": "+",
  "append": "+",
  "prepend": "+",
  "union": "+",
  "add-to-set": "+",
  "pair": ",",
  "minus": "-",
  "remove": "-",
  "remove-from-singleton": "-",
  "int-div": "/",
  "count": "/",
  "slice": ":",
  "step-range": ":",
  "assign-at-indices": ":",
  "sub": ":",
  "regex-sub": ":",
  "regex-search": ":",
  "regex-sub-group": ":",
  "regex-split": ":",
  "regex-matches-and-groups": ":",
  "end-everything": ";",
  "innermost-var": ";",
  "implicit-innermost-var": "",
  "less-than": "<",
  "less-than-lexi": "<",
  "prefix": "<",
  "all-but-suffix": "<",
  "less-than-abs": "<",
  "is-proper-subset": "<",
  "assign": "=",
  "augmented-assign": "=",
  "greater-than": ">",
  "suffix": ">",
  "all-but-prefix": ">",
  "greater-than-abs": ">",
  "is-proper-superset": ">",
  "ternary": "?",
  "if-then-else": "?",
  "index-into": "@",
  "lookup": "@",
  "intersection": "@",
  "root": "@",
  "assign-pair": "A",
  "break": "B",
  "bifurcate": "B",
  "char": "C",
  "conjugate": "C",
  "transpose": "C",
  "def": "D",
  "func-order-by": "D",
  "take-input": "E",
  "func-apply-repeatedly": "F",
  "func-fold": "F",
  "apply": "F",
  "for": "F",
  "alphabet-var": "G",
  "dict-var": "H",
  "if": "I",
  "func-invariant": "I",
  "set-var1": "J",
  "var1": "J",
  "set-var2": "J",
  "var2": "J",
  "def-func1": "L",
  "func1": "y",
  "func1-var": "b",
  "func-left-map": "L",
  "func-map": "M",
  "func-apply-map": "M",
  "def-func2": "M",
  "func2": "g",
  "func2-var1": "G",
  "func2-var2": "H",
  "quote": "N",
  "rand-int-below": "O",
  "rand-seed": "O",
  "rand-0-1": "O",
  "rand-float": "O",
  "rand-choice": "O",
  "prime-factors": "P",
  "is-prime": "P",
  "phase": "P",
  "remove-last": "P",
  "input": "Q",
  "implicit-assign-input": "",
  "implicit-input": "",
  "return": "R",
  "func-right-map": "R",
  "sort": "S",
  "sorted": "S",
  "unary-1-range": "S",
  "ten": "T",
  "unary-range": "U",
  "up-to-0": "U",
  "short-for": "V",
  "short-for-var": "N",
  "short-for-var1": "N",
  "short-for-var2": "H",
  "short-for-var3": "b",
  "vectorize": "V",
  "while": "W",
  "conditional-apply": "W",
  "assign-at": "X",
  "replace-at": "X",
  "translate": "X",
  "translate-flip": "X",
  "add-at": "X",
  "insert-at": "X",
  "empty-list-var": "Y",
  "zero-var": "Z",
  "list": "[",
  "literal-char": "\\",
  "singleton-list": "]",
  "power": "^",
  "repeated-cartesian-product": "^",
  "negate": "_",
  "reverse": "_",
  "swap-keys-vals": "_",
  "str-of": "`",
  "append-mutate": "a",
  "add-mutate": "a",
  "absolute-difference": "a",
  "newline": "b",
  "divide": "c",
  "split": "c",
  "split-whitespace": "c",
  "chop-into-size-n": "c",
  "chop-into-n-pieces": "c",
  "chop-at-indixes": "c",
  "space": "d",
  "end": "e",
  "end-digit": "e",
  "filter": "f",
  "filter-var": "T",
  "filter-var1": "T",
  "filter-var2": "Y",
  "filter-var3": "Z",
  "filter-above": "f",
  "filter-above-1": "f",
  "greater-than-or-equal-to": "g",
  "is-superset": "g",
  "inclusive-slice": "g",
  "head": "h",
  "increment": "h",
  "from-base": "i",
  "gcd": "i",
  "to-base": "j",
  "join": "j",
  "join-on-newline": "j",
  "empty-str-var": "k",
  "length": "l",
  "log-base-2": "l",
  "map": "m",
  "map-var": "d",
  "map-var1": "d",
  "map-var2": "k",
  "map-var3": "b",
  "not-equal": "n",
  "order-by": "o",
  "order-by-var": "N",
  "order-by-var1": "N",
  "order-by-var2": "Y",
  "print": "p",
  "implicit-print": "",
  "equal": "q",
  "lower": "r",
  "upper": "r",
  "swapcase": "r",
  "title": "r",
  "capitalize": "r",
  "capitalize-words": "r",
  "strip-whitespace": "r",
  "split-eval": "r",
  "rle": "r",
  "run-len-encode": "r",
  "run-len-string-decode": "r",
  "run-len-pair-decode": "r",
  "range": "r",
  "str-range": "r",
  "sum-strings": "s",
  "sum": "s",
  "flatten-once": "s",
  "int": "s",
  "decrement": "t",
  "tail": "t",
  "reduce": "u",
  "apply-repeatedly": "u",
  "fixed-point": "u",
  "reduce-var1": "G",
  "reduce-var2": "H",
  "reduce-var11": "G",
  "reduce-var12": "H",
  "reduce-var21": "N",
  "reduce-var22": "T",
  "eval": "v",
  "take-str-input": "w",
  "bitwise-xor": "x",
  "ind-in": "x",
  "ind-all-occurrences": "x",
  "powerset": "y",
  "subsets": "y",
  "double": "y",
  "implicit-assign-str-input": "",
  "str-input": "z",
  "deduplicate": "{",
  "or": "|",
  "in": "}",
  "inclusive-range": "}",
  "post-assign": "~",
  "augmented-post-assign": "~",
  "factorial": ".!",
  "gamma": ".!",
  "packed-str": ".",
  "bit-and": ".&",
  "pop-at": ".(",
  "pop": ".)",
  "splat": ".*",
  "deltas": ".+",
  "bag-minus": ".-",
  "partition": "./",
  "int-partition": "./",
  "substrings-of-len": ".:",
  "substrings-of-fraction": ".:",
  "substrings": ".:",
  "all-substrings": ".:",
  "rotate-left": ".<",
  "shift-left": ".<",
  "rotate-right": ".>",
  "shift-right": ".>",
  "else": ".?",
  "all": ".A",
  "bin": ".B",
  "combinations-with-replacement": ".C",
  "divmod": ".D",
  "delete": ".D",
  "delete-all": ".D",
  "any": ".E",
  "ceil": ".E",
  "format": ".F",
  "hex": ".H",
  "invert": ".I",
  "maxima": ".M",
  "maxima-var": "Z",
  "def-func3": ".N",
  "func3": ":",
  "func3-var1": "N",
  "func3-var2": "T",
  "func3-var3": "Y",
  "oct": ".O",
  "average": ".O",
  "permutations-of-len": ".P",
  "nth-permutation": ".P",
  "number-of-permutations": ".P",
  "all-evaluated-input": ".Q",
  "round-to-places": ".R",
  "round-like": ".R",
  "shuffle": ".S",
  "transpose-justified": ".T",
  "reduce-no-start": ".U",
  "infinite-for": ".V",
  "for-counting-up": ".V",
  "infinite-for-var": "b",
  "functional-while": ".W",
  "decompress": ".Z",
  "compress": ".Z",
  "left-pad": ".[",
  "sides-pad": ".[",
  "right-pad": ".[",
  "mod-exp": ".^",
  "prefixes": "._",
  "sign": "._",
  "abs": ".a",
  "l2-norm": ".a",
  "ls-norm-diff": ".a",
  "zip-map": ".b",
  "zip-map-var1": "N",
  "zip-map-var2": "Y",
  "combinations": ".c",
  "number-of-combinations": ".c",
  "system-time": ".d",
  "process-time": ".d",
  "detailed-time": ".d",
  "year": ".d",
  "month": ".d",
  "day": ".d",
  "hour": ".d",
  "second": ".d",
  "weekday": ".d",
  "sleep": ".d",
  "dict": ".d",
  "enumerate-map": ".e",
  "enumerate-map-var": "b",
  "enumerate-map-ind": "k",
  "filter-first-n": ".f",
  "filter-first-n-var": "Z",
  "group-by": ".g",
  "group-by-var": "k",
  "interleave": ".i",
  "complex": ".j",
  "log-base": ".l",
  "natural-log": ".l",
  "minima": ".m",
  "minima-var": "b",
  "flatten": ".n",
  "pi": ".n",
  "e": ".n",
  "sqrt-2": ".n",
  "phi": ".n",
  "infinity": ".n",
  "neg-infinity": ".n",
  "NaN": ".n",
  "all-permutations": ".p",
  "exit": ".q",
  "rotary-translate": ".r",
  "strip": ".s",
  "transpose-and-fill": ".t",
  "transpose-and-fill-with-spaces": ".t",
  "sin": ".t",
  "cos": ".t",
  "tan": ".t",
  "arcsin": ".t",
  "arccos": ".t",
  "arctan": ".t",
  "rad-to-deg": ".t",
  "deg-to-rad": ".t",
  "sinh": ".t",
  "cosh": ".t",
  "tanh": ".t",
  "arcsinh": ".t",
  "arccosh": ".t",
  "arctanh": ".t",
  "cumulative-reduce": ".u",
  "cumulative-fixed-point": ".u",
  "cumulative-reduce-var1": "N",
  "cumulative-reduce-var2": "Y",
  "eval-pyth": ".v",
  "write-file": ".w",
  "append-file": ".w",
  "write-image": ".w",
  "http-request": ".w",
  "try-catch": ".x",
  "all-input": ".z",
  "set": ".{",
  "bit-or": ".|",
  "set-union": ".|",
}


def translate(bigPyth):
    pyth = []
    for token in bigPyth.split():
        if token[0].isalpha() and token not in pythShrinker:
          print(f"""*** {token} is not a recognized token. Defaulting to literal "{token}\"""")
        pyth.append(pythShrinker.get(token, token))
    return "".join(pyth)

if __name__ == "__main__":
    # bigPyth = "".join(sys.stdin.readlines())
    with open(r"zz_makeProgram\z_big-pyth.txt", "r") as file:
      bigPyth = file.read()
    
    translateText = translate(bigPyth)

    print(translateText + "\n")

    inputText = input("immediate copy? ")

    if inputText and inputText.lower()[0] == "y":
      with open(r"zz_makeProgram\cool.py", "r") as file:
        bigContents = file.read().split("\n")

      bigContents[1] = 'r"""' + translateText + '"""'

      with open(r"zz_makeProgram\z_big-pyth.txt", "r") as file:
        bigContents[7] = file.read()