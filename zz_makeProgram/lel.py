code = \
r"""Jm0EVQ XEJ1;/J0"""

# code above
# big-pyth / readable version in doc-string below

"""
implicit-assign-input

implicit-assign
  auto-var
  map
    0
    take-input

short-for
  input
  no-print
    replace-at
      take-input
      auto-var
      1
end-everything

implicit-print
  count
    auto-var
    0
"""

# language resources:
# https://pyth.herokuapp.com/
# https://pyth.herokuapp.com/rev-doc.txt
# https://pyth.readthedocs.io/en/latest/
# https://tio.run/#pyth
# https://github.com/Hydrazer/pyth-programs/blob/main/zz_makeProgram/z_big-pyth.py

# nothing below bruh




















import sys
import copy as c
import io
import cmd
import traceback

sys.argv = ["python3", "pyth.py", "-cd", code]


class PythParseError(Exception):

    def __init__(self, active_char, rest_code):
        self.active_char = active_char
        self.rest_code = rest_code

    def __str__(self):
        return "%s is not implemented, %d from the end." % \
            (self.active_char, len(self.rest_code) + 1)


class UnsafeInputError(Exception):

    def __init__(self, active_char, rest_code):
        self.active_char = active_char
        self.rest_code = rest_code

    def __str__(self):
        return "%s is unsafe, %d from the end." % \
            (self.active_char, len(self.rest_code) + 1)

def str_parse_next(active_token):
    point = 0
    out = []
    while point < len(active_token):
        if active_token[point] == '\\':
            if len(active_token) == point + 1:
                out.append('\\\\')
                break
            elif active_token[point + 1] in ('\\', '"'):
                out.append(active_token[point:point+2])
                point += 2
                continue
            elif active_token[point + 1] == '\n':
                point += 2
                continue
        if active_token[point] == '\n':
            out.append('\\n')
        elif active_token[point] == '\r':
            out.append('\\r')
        elif active_token[point] == '\0':
            out.append('\\000')
        else:
            out.append(active_token[point])
        point += 1
    if out.count('"') == 1:
        out.append('"')
        assert out.count('"') == 2                
    return ''.join(out)


import binascii
import cmath
import collections
import copy
import datetime
import fractions
import functools
import hashlib
import itertools
import math
import numbers
import operator
import random
import re
import string
import sys
import time
import urllib.request
from ast import literal_eval
import zlib

# from data import c_to_f

# Type checking
def is_num(a):
    return isinstance(a, numbers.Number)


def is_seq(a):
    return isinstance(a, collections.Sequence)


def is_col(a):
    return isinstance(a, collections.Iterable)


def is_hash(a):
    return isinstance(a, collections.Hashable)


def is_lst(a):
    return isinstance(a, list) or isinstance(a, tuple)


# Error handling
class BadTypeCombinationError(Exception):

    def __init__(self, func, *args):
        self.args = args
        self.func = func

    def __str__(self):
        error_message = "\nError occured in function: %s" % self.func
        for i in range(len(self.args)):
            arg = self.args[i]
            arg_type = str(type(arg)).split("'")[1]
            error_message += "\nArg %d: %r, type %s." % (i + 1, arg, arg_type)
        return error_message


# Itertools type normalization
def itertools_norm(func, a, *args, **kwargs):
    if isinstance(a, str):
        return ["".join(group) for group in func(a, *args, **kwargs)]
    if isinstance(a, set):
        return [set(group) for group in func(a, *args, **kwargs)]
    else:
        return [list(group) for group in func(a, *args, **kwargs)]


def unknown_types(func, name, *args):
    if len(args) == 1:
        a, = args
        if is_seq(a) and not (isinstance(a, str) and len(a) == 1):
            return list(map(func, a))
    if len(args) == 2:
        a, b = args
        if is_seq(a) and not (isinstance(a, str) and len(a) == 1):
            return list(map(lambda left:func(left, b), a))
        elif is_seq(b) and not (isinstance(b, str) and len(b) == 1):
            return list(map(lambda right:func(a, right), b))
    raise BadTypeCombinationError(name, *args)

# The environment in which the generated Python code is run.
# All functions and all variables must be added to it.
environment = {}


# Infinite Iterator. Used in .f, .V
def infinite_iterator(start):
    def successor(char):
        if char.isalpha():
            if char == 'z':
                return 'a', True
            if char == 'Z':
                return 'A', True
            return chr(ord(char) + 1), False
        elif char.isdigit():
            if char == '9':
                return '0', True
            return chr(ord(char) + 1), False
        else:
            return chr(ord(char) + 1), False

    if is_num(start):
        while True:
            yield start
            start += 1

    # Replicates the behavior of ruby's .succ
    if isinstance(start, str):
        while True:
            yield start
            alphanum_locs = [loc for loc in range(len(start))
                             if start[loc].isalnum() and ord(start[loc]) < 128]
            if alphanum_locs:
                locs = alphanum_locs[::-1]
            elif start:
                locs = range(len(start))[::-1]
            else:
                locs = []
                succ_char = 'a'
            for inc_loc in locs:
                inc_char = start[inc_loc]
                succ_char, carry = successor(inc_char)
                start = start[:inc_loc] + succ_char + start[inc_loc + 1:]
                if not carry:
                    break
            else:
                start = succ_char + start

    raise BadTypeCombinationError("infinite_iterator, probably .V", start)
environment['infinite_iterator'] = infinite_iterator


# memoizes function calls, key = repr of input.
class memoized(object):

    def __init__(self, func):
        self.func = func
        self.cache = {}

    def __call__(self, *args):
        args_repr = repr(args)
        if args_repr in self.cache:
            return self.cache[args_repr]
        else:
            value = self.func(*args)
            self.cache[args_repr] = value
            return value
environment['memoized'] = memoized


# If argument is a number, turn it into a range.
def num_to_range(arg):
    if isinstance(arg, int) and arg > 0:
        return range(arg)
    if is_num(arg):
        return urange(arg)

    return arg
environment['num_to_range'] = num_to_range


# Implicit print
def imp_print(a):
    if a is not None:
        print(a)
    return a
environment['imp_print'] = imp_print


# F on unary function. Repeated application.
def repeat(func, start, repetitions):
    if not isinstance(repetitions, int):
        raise BadTypeCombinationError("F", repetitions, start)
    value = start
    for _ in range(repetitions):
        value = func(value)
    return value
environment['repeat'] = repeat


# F on binary function. Fold.
def fold(func, lst):
    if func == environment[c_to_f['*'][0]]:
        if not lst:
            return 1
        if not is_col(lst): 
            return factorial(lst)
    if not lst:
        if func == environment[c_to_f['+'][0]]:
            return []
        else:
            return 0
    return reduce2(func, lst)
environment['fold'] = fold


# Lookup from the environment, ignoring lambdas.
def env_lookup(var):
    return environment[var]
environment['env_lookup'] = env_lookup


# Function library. See data for letter -> function correspondences.
# =. N/A
def assign(a, b):
    if isinstance(a, str):
        if len(a) == 1:
            environment[a] = copy.deepcopy(b)
            return environment[a]
        else:
            var_names = a.strip('[]').split(',')
            if is_seq(b) and len(var_names) == len(b) == 2 and \
                    all(len(var_name) == 1 for var_name in var_names):
                output = []
                for var_name, item in zip(var_names, b):
                    environment[var_name] = copy.deepcopy(item)
                    output.append(environment[var_name])
                return output
    raise BadTypeCombinationError("=", a, b)
environment['assign'] = assign


# ~. N/A
def post_assign(a, b):
    if isinstance(a, str):
        if len(a) == 1:
            old_a = environment[a]
            environment[a] = copy.deepcopy(b)
            return old_a
    raise BadTypeCombinationError("~", a, b)
environment['post_assign'] = post_assign


# !. All.
def Pnot(a):
    return not a
environment['Pnot'] = Pnot


# @.
def lookup(a, b):
    if is_num(a) and is_num(b):
        return a ** (1 / b)
    if isinstance(a, dict):
        if isinstance(b, list):
            b = tuple(b)
        return a[b]
    if is_seq(a) and isinstance(b, int):
        return a[b % len(a)]
    if is_col(a) and is_col(b):
        if isinstance(a, str):
            intersection = [b_elem for  b_elem in b
                            if isinstance(b_elem, str) and b_elem in a]
        else:
            intersection = [b_elem for b_elem in b if b_elem in a]
        if isinstance(a, str):
            return ''.join(intersection)
        if isinstance(a, set):
            return set(intersection)
        else:
            return list(intersection)
    return unknown_types(lookup, "@", a, b)
environment['lookup'] = lookup


# %. int, str.
def mod(a, b):
    if isinstance(a, int) and is_seq(b):
        return b[::a]
    if isinstance(a, complex) and is_num(b):
        return (a.real % b) + (a.imag % b) * 1j
    if is_num(a) and is_num(b):
        return a % b
    if isinstance(a, str):
        if is_lst(b):
            return a % tuple(b)
        else:
            return a % b
    return unknown_types(mod, "%", a, b)
environment['mod'] = mod


# ^. int, str, list.
def Ppow(a, b):
    if is_num(a) and is_num(b):
        return pow(a, b)
    if is_col(a) and isinstance(b, int):
        return itertools_norm(itertools.product, a, repeat=b)

    return unknown_types(Ppow, "^", a, b)
environment['Ppow'] = Ppow


# *. int, str, list.
def times(a, b):
    if is_col(a) and is_col(b):
        prod = list(itertools.product(a, b))
        if isinstance(a, str) and isinstance(b, str):
            return[''.join(pair) for pair in prod]
        else:
            return [list(pair) for pair in prod]
    if is_num(a) and is_num(b):
        return a * b
    if isinstance(a, int) and is_seq(b):
        return a * b
    if is_seq(a) and isinstance(b, int):
        if b < 0:
            return -b * a[::-1]
        else:
            return a * b
    return unknown_types(times, "*", a, b)
environment['times'] = times


# (. All types
def Ptuple(*a):
    return a
environment['Ptuple'] = Ptuple


# -. int, set.
def minus(a, b):
    if is_num(a) and is_num(b):
        return a - b
    if is_num(a) and is_col(b):
        if isinstance(b, str):
            return minus(str(a), b)
        if is_lst(b):
            return minus([a], b)
        if isinstance(b, set):
            return minus({a}, b)
    if is_num(b) and is_col(a):
        if isinstance(a, str):
            return minus(a, str(b))
        if is_lst(a):
            return minus(a, [b])
        if isinstance(a, set):
            return minus(a, {b})
    if is_col(a) and is_col(b):
        if isinstance(b, str):
            difference = [c for c in a if not isinstance(c, str) or c not in b]
        else:
            difference = [c for c in a if c not in b]
        if isinstance(a, str):
            return ''.join(difference)
        if is_lst(a):
            return list(difference)
        if isinstance(a, set):
            return set(difference)
    return unknown_types(minus, "-", a, b)
environment['minus'] = minus


# '. str.
def read_file(a):
    if isinstance(a, str):
        if any(a.lower().endswith("." + i) for i in
               ["png", "jpg", "jpeg", "gif", "svg", "ppm", "pgm", "pbm"]):
            from PIL import Image
            img = Image.open(a)
            data = list(img.getdata())

            # If alpha all 255, take out alpha
            if len(data[0]) > 3 and all(i[3] == 255 for i in data):
                data = [i[:3] for i in data]

            # Check grayscale
            if all(i.count(i[0]) == len(i) for i in data):
                data = [i[0] for i in data]

            data = chop(data, img.size[0])
            return data

        if a.startswith("http"):
            b = list(map(str, urllib.request.urlopen(a)))
        else:
            b = open(a)

        b = [lin[:-1] if lin[-1] == '\n' else lin for lin in b]
        return b

    return unknown_types(read_file, "'", a)
environment['read_file'] = read_file


# _. All.
def neg(a):
    if is_num(a):
        return -a
    if is_seq(a):
        return a[::-1]
    if isinstance(a, dict):
        return {value: key for key, value in a.items()}
    return unknown_types(neg, "_", a)
environment['neg'] = neg


# {. All.
def uniquify(a):
    if is_seq(a):
        try:
            seen = set()
            out = []
            for elem in a:
                if not elem in seen:
                    out.append(elem)
                    seen.add(elem)
        except TypeError:
            out = []
            for elem in a:
                if not elem in out:
                    out.append(elem)
        if isinstance(a, str):
            return ''.join(out)
        return out
    if is_col(a):
        return sorted(a)
    return unknown_types(uniquify, '{', a)
environment['uniquify'] = uniquify


# }. in
def Pin(a, b):
    if isinstance(a, int) and isinstance(b, int):
        if a < b:
            return list(range(a, b + 1))
        return list(range(b, a + 1))[::-1]
    if is_col(b):
        return a in b
    return unknown_types(Pin, '}', a, b)
environment['Pin'] = Pin


# +. All.
def plus(a, b):
    if isinstance(a, set):
        if is_col(b):
            return a.union(b)
        else:
            return a.union({b})
    if is_lst(a) and not is_lst(b):
        return list(a) + [b]
    if is_lst(b) and not is_lst(a):
        return [a] + list(b)
    if is_lst(a) and is_lst(b):
        return list(a) + list(b)
    if is_num(a) and is_num(b) or\
            isinstance(a, str) and isinstance(b, str):
        return a + b
    if is_num(a) and isinstance(b, str):
        return str(a) + b
    if isinstance(a, str) and is_num(b):
        return a + str(b)
    return unknown_types(plus, "+", a, b)
environment['plus'] = plus


# [. All.
def Plist(*a):
    return list(a)
environment['Plist'] = Plist

# ]. All.
def singleton(a):
    return [a]
environment['singleton'] = singleton

# :. list.
def at_slice(a, b, c=0):
    if isinstance(a, str) and isinstance(b, str):
        if isinstance(c, str):
            return re.sub(b, c, a)
        if c == 0:
            return bool(re.search(b, a))
        if c == 1:
            return [m.group(0) for m in re.finditer(b, a)]
        if c == 2:
            def first_group(matchobj):
                return matchobj.group(1)
            return re.sub(b, first_group, a)
        if c == 3:
            return re.split(b, a)
        if c == 4:
            return [[m.group(0)] + list(m.groups()) for m in re.finditer(b, a)]
        return unknown_types(at_slice, ":", a, b, c)
    if is_seq(a) and isinstance(b, int) and isinstance(c, int):
        return a[slice(b, c)]

    if is_num(a) and is_num(b) and is_num(c):
        if c > 0:
            work = a
            gen_range = []
            if a <= b:
                def cont_test(work):
                    return work < b
                step = c
            else:
                def cont_test(work):
                    return work > b
                step = -c
            while cont_test(work):
                gen_range.append(work)
                work += step
            return gen_range
        elif c < 0:
            return at_slice(b, a, -c)[::-1]

    # There is no nice ABC for this check.
    if hasattr(a, "__getitem__") and is_col(b):
        if is_col(c):
            rep_c = itertools.cycle(c)
        else:
            rep_c = itertools.repeat(c)

        if isinstance(a, str) or isinstance(a, tuple):
            indexable = list(a)
        else:
            indexable = a

        for repl_index in b:
            if isinstance(a, str):
                indexable[repl_index] = str(next(rep_c))
            else:
                indexable[repl_index] = next(rep_c)

        if isinstance(a, str):
            return "".join(indexable)

        return indexable

    return unknown_types(at_slice, ":", a, b, c)
environment['at_slice'] = at_slice


# <. All.
def lt(a, b):
    if isinstance(a, set) and is_col(b):
        return a.issubset(b) and a != b
    if is_seq(a) and isinstance(b, int):
        return a[:b]
    if isinstance(a, int) and is_seq(b):
        if a >= len(b):
            if isinstance(b, str):
                return ''
            else:
                return []
        return b[:len(b) - a]
    if isinstance(a, complex) or isinstance(b, complex):
        return abs(a) < abs(b)
    if is_num(a) and is_num(b) or\
            isinstance(a, list) and isinstance(b, list) or\
            isinstance(a, tuple) and isinstance(b, tuple) or\
            isinstance(a, str) and isinstance(b, str):
        return a < b
    return unknown_types(lt, "<", a, b)
environment['lt'] = lt


# >. All.
def gt(a, b):
    if isinstance(a, set) and is_col(b):
        return a.issuperset(b) and a != b
    if is_seq(a) and isinstance(b, int):
        return a[b:]
    if isinstance(a, int) and is_seq(b):
        if a >= len(b):
            return b
        return b[len(b) - a:]
    if isinstance(a, complex) or isinstance(b, complex):
        return abs(a) > abs(b)
    if is_num(a) and is_num(b) or\
            isinstance(a, list) and isinstance(b, list) or\
            isinstance(a, tuple) and isinstance(b, tuple) or\
            isinstance(a, str) and isinstance(b, str):
        return a > b
    return unknown_types(gt, ">", a, b)
environment['gt'] = gt


# /. All.
def div(a, b):
    if is_num(a) and is_num(b):
        return int(a // b)
    if is_seq(a):
        return a.count(b)
    return unknown_types(div, "/", a, b)
environment['div'] = div


# a. List, Set.
def append(a, b):
    if isinstance(a, list):
        a.append(b)
        return a
    if isinstance(a, set):
        if is_hash(b):
            a.add(b)
            return a
        else:
            a.add(tuple(b))
            return a
    if is_num(a) and is_num(b):
        return abs(a - b)
    return unknown_types(append, "a", a, b)
environment['append'] = append

environment['b'] = "\n"


# c. All
def chop(a, b=None):
    if is_num(a) and is_num(b):
        return a / b
    if isinstance(a, str) and isinstance(b, str):
        return a.split(b)
    if isinstance(a, str) and b is None:
        return a.split()
    # iterable, int -> chop a into pieces of length b
    if is_seq(a) and isinstance(b, int):
        return [a[i:i + b] for i in range(0, len(a), b)]
    # int, iterable -> split b into a pieces (distributed equally)
    if isinstance(a, int) and is_seq(b):
        m = len(b) // a  # min number of elements
        r = len(b) % a   # remainding elements
        begin_ind, end_ind = 0, m + (r > 0)
        l = []
        for i in range(a):
            l.append(b[begin_ind:end_ind])
            begin_ind, end_ind = end_ind, end_ind + m + (i + 1 < r)
        return l
    # seq, col of ints -> chop seq at number locations.
    if is_seq(a) and is_col(b):
        if all(isinstance(elem, int) for elem in b) and not isinstance(b, str):
            locs = sorted(b)
            return [a[i:j] for i, j in zip([0] + locs, locs + [len(a)])]
    if is_seq(a):
        output = [[]]
        for elem in a:
            if elem == b:
                output.append([])
            else:
                output[-1].append(elem)
        return output
    return unknown_types(chop, "c", a, b)
environment['chop'] = chop


# C. int, str.
def Pchr(a):
    if isinstance(a, int):
        try:
            return chr(a)
        except (ValueError, OverflowError):
            return ''.join(chr(digit) for digit in from_base_ten(a, 256))
    if isinstance(a, complex):
        return a.real - a.imag * 1j
    if is_num(a):
        return Pchr(int(a))
    if isinstance(a, str):
        return to_base_ten([ord(char) for char in a], 256)
    if is_col(a):
        trans = list(zip(*a))
        if all(isinstance(sublist, str) for sublist in a):
            return [''.join(row) for row in trans]
        else:
            return [list(row) for row in trans]
    return unknown_types(Pchr, "C", a)
environment['Pchr'] = Pchr


environment['d'] = ' '


# e. All.
def end(a):
    if isinstance(a, complex):
        return a.imag
    if is_num(a):
        return a % 10
    if is_seq(a):
        return a[-1]
    return unknown_types(end, "e", a)
environment['end'] = end


# E.
def eval_input():
    return literal_eval(input())
environment['eval_input'] = eval_input


# f. single purpose.
def Pfilter(a, b=1):
    if is_num(b):
        return next(counter for counter in itertools.count(b) if a(counter))
    if is_col(b):
        return list(filter(a, b))
    return unknown_types(Pfilter, "f", a, b)
environment['Pfilter'] = Pfilter
environment['G'] = string.ascii_lowercase


# g. All.
def gte(a, b):
    if isinstance(a, set) and is_col(b):
        return a.issuperset(b)
    if is_seq(a) and isinstance(b, int):
        return a[b - 1:]
    if is_num(a) and is_num(b) or\
            isinstance(a, list) and isinstance(b, list) or\
            isinstance(a, tuple) and isinstance(b, tuple) or\
            isinstance(a, str) and isinstance(b, str):
        return a >= b
    return unknown_types(gte, "g", a, b)
environment['gte'] = gte
environment['H'] = {}


# h. int, str, list.
def head(a):
    if is_num(a):
        return a + 1
    if is_seq(a):
        return a[0]
    return unknown_types(head, "h", a)
environment['head'] = head


# i. int, str
def base_10(a, b):
    if isinstance(a, str) and isinstance(b, int):
        if not a:
            return 0
        return int(a, b)
    if is_seq(a) and is_num(b):
        return to_base_ten(a, b)
    if isinstance(a, int) and isinstance(b, int):
        return fractions.gcd(a, b)
    return unknown_types(base_10, "i", a, b)
environment['base_10'] = base_10


def to_base_ten(arb, base):
    # Special cases
    if abs(base) == 1:
        return len(arb)
    if len(arb) < 2:
        return arb[0] if arb else 0
    digits = []
    it = iter(arb)
    if len(arb) % 2 != 0:
        digits.append(next(it))
    for digit in it:
        digits.append(digit * base + next(it))
    return to_base_ten(digits, base * base)


# j. str.
def join(a, b=None):
    if b is None:
        a, b = '\n', a
    if isinstance(a, int) and isinstance(b, int):
        return from_base_ten(a, b)
    if isinstance(a, str) and is_col(b):
        return a.join(list(map(str, b)))
    if is_col(b):
        return str(a).join(list(map(str, b)))
    return unknown_types(join, "j", a, b)
environment['join'] = join


def from_base_ten(arb, base):
    # Special cases
    if arb == 0:
        return [0]
    if abs(base) == 1:
        return [0] * arb
    # Main routine
    base_list = []
    it = reversed(from_base_ten(arb, base * base) if abs(arb) >= abs(base) else [arb])
    digit = next(it)
    clock = 0
    work = 0
    while clock >= 0 or work != 0:
        if clock == 0:
            work += digit
            try:
                digit = next(it)
                clock = 2
            except StopIteration:
                digit = 0
        clock -= 1
        work, remainder = divmod(work, base)
        if remainder < 0:
            work += 1
            remainder -= base
        if work == -1 and base > 0:
            work = 0
            remainder -= base
        base_list.append(remainder)
    return base_list[::-1]

environment['k'] = ''


# l. any
def Plen(a):
    if is_num(a):
        if isinstance(a, complex) or a < 0:
            return cmath.log(a, 2)
        return math.log(a, 2)

    if is_col(a):
        return len(a)
    return unknown_types(Plen, "l", a)
environment['Plen'] = Plen


# m. Single purpose.
def Pmap(a, b):
    if is_num(b):
        return list(map(a, urange(b)))
    if is_col(b):
        return list(map(a, b))
    return unknown_types(Pmap, "m", a, b)
environment['Pmap'] = Pmap
environment['N'] = '"'


# n. All.
def ne(a, b):
    return not equal(a, b)
environment['ne'] = ne


# O. int, str, list
def rchoice(a):
    if isinstance(a, int):
        if a == 0:
            return random.random()
        if a < 0:
            random.seed(-a)
            return
        if a > 0:
            return random.randrange(a)
    if is_num(a):
        # random.uniform works for both complex and float
        return random.uniform(0, a)
    if is_seq(a):
        return random.choice(a)
    if is_col(a):
        return random.choice(list(a))
    return unknown_types(rchoice, "O", a)
environment['rchoice'] = rchoice


# o. Single purpose.
def order(a, b):
    if is_num(b):
        b = urange(b)
    if is_col(b):
        if isinstance(b, str):
            return ''.join(sorted(b, key=a))
        else:
            return sorted(b, key=a)
    return unknown_types(order, "o", a, b)
environment['order'] = order


# P. int, str, list.
def primes_pop(a):
    if isinstance(a, int):
        if a < 0:
            # Primality testing
            return len(primes_pop(-a)) == 1
        if a < 2:
            return []
        def simple_factor(a):
            working = a
            output = []
            num = 2
            while num * num <= working:
                while working % num == 0:
                    output.append(num)
                    working //= num
                num += 1
            if working != 1:
                output.append(working)
            return output
        if a < 10 ** 4:
            return simple_factor(a)
        else:
            try:
                from sympy import factorint
                factor_dict = factorint(a)
                factors_with_mult = [[fact for _ in range(
                    factor_dict[fact])] for fact in factor_dict]
                return sorted(sum(factors_with_mult, []))
            except:
                return simple_factor(a)
    if is_num(a):
        return cmath.phase(a)
    if is_seq(a):
        return a[:-1]
    return unknown_types(primes_pop, "P", a)
environment['primes_pop'] = primes_pop


# p. All.
def Pprint(a):
    print(a, end='')
    return a
environment['Pprint'] = Pprint


# q. All.
def equal(a, b):
    return a == b
environment['equal'] = equal


# r. int, int or str,int.
def Prange(a, b):
    def run_length_encode(a):
        return [[len(list(group)), key] for key, group in itertools.groupby(a)]

    if isinstance(b, int):
        if isinstance(a, str):
            if b == 0:
                return a.lower()
            if b == 1:
                return a.upper()
            if b == 2:
                return a.swapcase()
            if b == 3:
                return a.title()
            if b == 4:
                return a.capitalize()
            if b == 5:
                return string.capwords(a)
            if b == 6:
                return a.strip()
            if b == 7:
                return [Pliteral_eval(part) for part in a.split()]
            if b == 8:
                return run_length_encode(a)
            if b == 9:
                # Run length decoding, format "<num><char><num><char>",
                # e.g. "12W3N6S1E"
                return re.sub(r'(\d+)(\D)',
                              lambda match: int(match.group(1))
                              * match.group(2), a)

        if is_seq(a):
            if b == 8:
                return run_length_encode(a)
            if b == 9:
                if all(isinstance(key, str) for group_size, key in a):
                    return ''.join(key * group_size for group_size, key in a)
                else:
                    return sum(([copy.deepcopy(key)] * group_size
                                for group_size, key in a), [])
            return unknown_types(Prange, "r", a, b)

        if isinstance(a, int):
            if a < b:
                return list(range(a, b))
            else:
                return list(range(a, b, -1))
        return unknown_types(Prange, "r", a, b)
    if isinstance(a, str) and isinstance(b, str):
        a_val = Pchr(a)
        b_val = Pchr(b)
        ab_range = Prange(a_val, b_val)
        return [''.join(chr(char_val) for char_val in join(str_val, 256))
                for str_val in ab_range]
    if isinstance(a, int) and is_seq(b):
        return Prange(b, a)
    return unknown_types(Prange, "r", a, b)
environment['Prange'] = Prange


# s. int, str, list.
def Psum(a):
    if is_col(a) and not isinstance(a, str):
        if len(a) == 0:
            return 0
        if all(isinstance(elem, str) for elem in a):
            return ''.join(a)
        if len(a) > 100:
            cutoff = len(a) // 2
            first = a[:cutoff]
            second = a[cutoff:]
            return plus(Psum(first), Psum(second))
        return reduce(lambda b, c: plus(b, c), a[1:], a[0])
    if isinstance(a, complex):
        return a.real
    if a == '':
        return 0
    if is_num(a) or isinstance(a, str):
        return int(a)
    return unknown_types(Psum, "s", a)
environment['Psum'] = Psum


# S. seq
def Psorted(a):
    if isinstance(a, str):
        return ''.join(sorted(a))
    if is_col(a):
        return sorted(a)
    if isinstance(a, int):
        return list(range(1, a + 1))
    if is_num(a):
        return Psorted(int(a))
    return unknown_types(Psorted, "S", a)
environment['Psorted'] = Psorted
environment['T'] = 10


# t. int, str, list.
def tail(a):
    if is_num(a):
        return a - 1
    if is_seq(a):
        return a[1:]
    return unknown_types(tail, "t", a)
environment['tail'] = tail


# u. single purpose
def reduce(a, b, c=None):
    # Fixed point / Loop
    if c is None:
        counter = 0
        results = [copy.deepcopy(b)]
        acc = a(b, counter)
        while acc not in results:
            counter += 1
            results.append(copy.deepcopy(acc))
            acc = a(acc, counter)
        return copy.deepcopy(acc)

    # Reduce
    if is_seq(b) or is_num(b):
        if is_num(b):
            seq = urange(b)
        else:
            seq = b
        acc = c
        while len(seq) > 0:
            h = seq[0]
            acc = a(acc, h)
            seq = seq[1:]
        return acc
    return unknown_types(reduce, "u", a, b, c)
environment['reduce'] = reduce


# U. int, str, list.
def urange(a):
    if isinstance(a, int):
        if a >= 0:
            return list(range(a))
        else:
            return list(range(a, 0))
    if is_num(a):
        return urange(int(a))
    if is_col(a):
        return list(range(len(a)))
    return unknown_types(urange, "U", a)
environment['urange'] = urange


# v. str.
def preprocess_eval(a):
    if isinstance(a, str):
        if a and a[0] == '0':
            to_eval = a.lstrip('0')
            if not to_eval or not to_eval[0].isdecimal():
                to_eval = '0' + to_eval
            return to_eval
        else:
            return a
    return unknown_types(preprocess_eval, 'v', a)


def Pliteral_eval(a):
    if isinstance(a, str):
        return literal_eval(preprocess_eval(a))
    return unknown_types(Pliteral_eval, 'v', a)
environment['Pliteral_eval'] = Pliteral_eval


def Punsafe_eval(a):
    if isinstance(a, str):
        return eval(preprocess_eval(a))
    return unknown_types(Punsafe_eval, 'v', a)
environment['Punsafe_eval'] = Punsafe_eval


# X.
def assign_at(a, b, c=None):
    # Assign at
    if isinstance(a, dict):
        if isinstance(b, list):
            b = tuple(b)
        a[b] = c
        return a
    if isinstance(b, int):
        if isinstance(a, list):
            a[b % len(a)] = c
            return a
        if isinstance(a, str):
            return a[:b % len(a)] + str(c) + a[(b % len(a)) + 1:]
        if isinstance(a, tuple):
            return a[:b % len(a)] + (c,) + a[(b % len(a)) + 1:]
        return unknown_types(assign_at, "X", a, b, c)
    # Translate
    if is_seq(a) and is_seq(b) and (c is None or is_seq(c)):
        if c is None:
            c = b[::-1]

        def trans_func(element):
            return c[b.index(element) % len(c)] if element in b else element
        translation = map(trans_func, a)
        if isinstance(a, str) and isinstance(c, str):
            return ''.join(translation)
        else:
            return list(translation)
    # += in a list, X<int><list><any>
    if isinstance(a, int) and is_lst(b):
        b[a % len(b)] = plus(b[a % len(b)], c)
        return b
    # += in a dict, X<any><dict><any>
    if isinstance(b, dict):
        if isinstance(a, list):
            a = tuple(a)
        if a in b:
            b[a] = plus(b[a], c)
        else:
            b[a] = c
        return b
    # Insert in a string, X<int><str><any>
    if isinstance(a, int) and isinstance(b, str):
        if not isinstance(c, str):
            c = str(c)
        return b[:a] + c + b[a:]
    return unknown_types(assign_at, "X", a, b, c)
environment['assign_at'] = assign_at


# x. int, str, list.
def index(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return a ^ b
    if is_seq(a) and not (isinstance(a, str) and not isinstance(b, str)):
        if b in a:
            return a.index(b)
        # replicate functionality from str.find
        else:
            return -1
    if is_lst(b):
        return [index for index, elem in enumerate(b) if elem == a]
    if isinstance(a, str):
        return index(a, str(b))
    return unknown_types(index, "x", a, b)
environment['index'] = index


# y. string, list.
def subsets(a):
    if is_num(a):
        return a * 2
    if is_col(a):
        def powerset(col):
            return itertools.chain.from_iterable(
                itertools.combinations(col, i) for i in range(0, len(col) + 1))
        return itertools_norm(powerset, a)
    return unknown_types(subsets, "y", a)
environment['subsets'] = subsets


environment['Y'] = []
environment['Z'] = 0


def hash_repr(a):
    if isinstance(a, bool):
        return "1" if a else "0"

    if isinstance(a, str) or is_num(a):
        return repr(a)

    if isinstance(a, list) or isinstance(a, tuple):
        return "[{}]".format(", ".join(hash_repr(l) for l in a))

    if isinstance(a, set):
        return "[{}]".format(", ".join(hash_repr(l) for l in sorted(a)))

    if isinstance(a, dict):
        elements = ["({}, {})".format(hash_repr(k), hash_repr(a[k]))
                    for k in sorted(a)]
        return "[{}]".format(", ".join(elements))

    return unknown_types(hash_repr, ".h", a)


def hex_multitype(a, func):
    if isinstance(a, str):
        return "0x" + (binascii.hexlify(a.encode("utf-8")).decode("utf-8") or "0")

    if isinstance(a, int):
        return hex(a)

    return unknown_types(hex_multitype, func, a)


# .h. any
def Phash(a):
    return int(hashlib.sha256(hash_repr(a).encode("utf-8")).hexdigest(), 16)
environment['Phash'] = Phash


# .a num/seq of num/seq of 2 seq of num
def Pabs(a):
    if is_num(a):
        return abs(a)
    if isinstance(a, tuple) or isinstance(a, list):
        if not a:
            return 0
        if is_num(a[0]):
            return sum(num ** 2 for num in a) ** .5
        if len(a) == 2:
            return sum((num1 - num2) ** 2 for num1, num2 in zip(*a)) ** .5

    return unknown_types(Pabs, ".a", a)
environment['Pabs'] = Pabs


# .b lambda, 2 ints or cols
def binary_map(a, b, c=None):
    if c is None:
        b, c = zip(*b)
    if is_num(b):
        b = urange(b)
    if is_num(c):
        c = urange(c)
    if is_col(b) and is_col(c):
        return list(map(a, b, c))
    return unknown_types(binary_map, ".b", a, b, c)
environment['binary_map'] = binary_map


# .B. int/str
def Pbin(a):
    if isinstance(a, int) or isinstance(a, str):
        return bin(int(hex_multitype(a, ".B"), 16))[2:]
    return unknown_types(Pbin, ".B", a)
environment['Pbin'] = Pbin


# .c. seq, int
def combinations(a, b):
    if isinstance(a, int) and isinstance(b, int):
        # compute n C r
        n, r = a, min(b, a - b)
        if r == 0:
            return 1
        if r < 0:
            r = max(b, a - b)
            if r < 0:
                return 0

        num = functools.reduce(operator.mul, range(n, n - r, -1), 1)
        den = math.factorial(r)

        return num // den

    if is_col(a) and isinstance(b, int):
        return itertools_norm(itertools.combinations, a, b)

    return unknown_types(combinations, ".c", a, b)

environment['combinations'] = combinations


# .C. iter, int
def combinations_with_replacement(a, b):
    if not is_col(a) or not isinstance(b, int):
        return unknown_types(combinations_with_replacement, ".C", a, b)

    return itertools_norm(itertools.combinations_with_replacement, a, b)
environment['combinations_with_replacement'] = combinations_with_replacement


# .d num, list of 2-elem lists
def dict_or_date(a):
    if isinstance(a, int):
        if a == 0:
            return time.time()
        if a == 1:
            return time.process_time()
        if 2 <= a <= 9:
            today = datetime.datetime.now()
            attributes = [today.year,
                          today.month,
                          today.day,
                          today.hour,
                          today.minute,
                          today.second,
                          today.microsecond]
            if a == 2:
                return attributes
            if a < 9:
                return attributes[a - 3]
            if a == 9:
                return today.weekday()
    if is_num(a):
        time.sleep(abs(a))
        return
    if is_col(a):
        return dict(a)
    return unknown_types(dict_or_date, ".d", a)
environment['dict_or_date'] = dict_or_date


# .D num, num or seq, int or seq, col
def divmod_or_delete(a, b):
    if is_num(a) and is_num(b):
        return list(divmod(a, b))
    elif is_seq(a) and is_num(b):
        return divmod_or_delete(a, [b])
    elif is_seq(a) and is_col(b):
        output = [e for i, e in enumerate(a) if i not in b]
        if isinstance(a, str):
            return "".join(output)
        return output
    return unknown_types(divmod_or_delete, '.D', a, b)
environment['divmod_or_delete'] = divmod_or_delete


# .e. lambda, seq
def Penumerate(a, b):
    if is_col(b):
        return list(map(lambda arg: a(*arg), enumerate(b)))

    return unknown_types(Penumerate, ".e", a, b)
environment['Penumerate'] = Penumerate


# .E. col/num
def Pany(a):
    if is_col(a):
        return any(a)
    if is_num(a):
        return int(math.ceil(a))
    return unknown_types(Pany, ".E", a)
environment['Pany'] = Pany


# .f. lambda, int, num or str.
def first_n(a, b, c=1):
    if not isinstance(b, int):
        return unknown_types(first_n, ".f", a, b, c)
    if is_num(c) or isinstance(c, str):
        return list(itertools.islice(filter(a, infinite_iterator(c)), b))
    elif is_col(c):
        return list(itertools.islice(filter(a, c), b))
    return unknown_types(first_n, ".f", a, b, c)
environment['first_n'] = first_n


# .F. format
def Pformat(a, b):
    if not isinstance(a, str):
        return unknown_types(Pformat, ".F", a, b)
    if is_seq(b) and not isinstance(b, str):
        return a.format(*b)

    return a.format(b)
environment['Pformat'] = Pformat


# .g lambda, seq
def group_by(a, b):
    if is_num(b):
        seq = urange(b)
    elif is_col(b):
        seq = b
    else:
        return unknown_types(group_by, ".g", a, b)
    key_sort = sorted(seq, key=a)
    grouped = itertools.groupby(key_sort, key=a)
    if isinstance(b, str):
        return list(map(lambda group: ''.join(group[1]), grouped))
    else:
        return list(map(lambda group: list(group[1]), grouped))
environment['group_by'] = group_by


# .H. int/str
def Phex(a):
    if isinstance(a, int) or isinstance(a, str):
        return hex_multitype(a, ".H")[2:]
    return unknown_types(Phex, ".H", a)
environment['Phex'] = Phex


# .i. seq, seq
def interleave(a, b):
    if is_seq(a) and is_seq(b):
        overlap = min(len(a), len(b))
        longer = max((a, b), key=len)
        inter_overlap = [item for sublist in zip(a, b) for item in sublist]
        if isinstance(a, str) and isinstance(b, str):
            return ''.join(inter_overlap) + longer[overlap:]
        else:
            return inter_overlap + list(longer[overlap:])
    if is_col(a) and not is_seq(a):
        return interleave(sorted(list(a)), b)
    if is_col(b) and not is_seq(b):
        return interleave(a, sorted(list(b)))
    return unknown_types(interleave, ".i", a, b)
environment['interleave'] = interleave


# .I. lambda, any
def invert(a, b):
    if not is_num(b):
        return unknown_types(invert, ".I", a, b)
    inv = 1.
    if a(inv) == b:
        return inv
    while a(inv) < b:
        inv *= 2
    delta = inv / 2
    while delta > 1e-20:
        if a(inv) == b:
            return inv
        if a(inv - delta) > b:
            inv -= delta
        elif a(inv - delta) == b:
            return inv - delta
        delta /= 2
    return inv
environment['invert'] = invert


# .j. int, int
def Pcomplex(a=0, b=1):
    if not is_num(a) and is_num(b):
        return unknown_types(Pcomplex, ".j", a, b)
    return a + b * complex(0, 1)
environment['Pcomplex'] = Pcomplex


# .l. num, num
def log(a, b=math.e):
    if not is_num(a) or not is_num(b):
        return unknown_types(log, ".l", a, b)
    if a < 0:
        return cmath.log(a, b)

    return math.log(a, b)
environment['log'] = log


# .m. func, seq or int
def minimal(a, b):
    if is_num(b):
        seq = urange(b)
    elif is_col(b):
        seq = b
    else:
        return unknown_types(minimal, ".m", a, b)
    minimum = min(map(a, seq))
    return list(filter(lambda elem: a(elem) == minimum, seq))
environment['minimal'] = minimal


# .M. func, seq or int
def maximal(a, b):
    if is_num(b):
        seq = urange(b)
    elif is_col(b):
        seq = b
    else:
        return unknown_types(maximal, ".M", a, b)
    maximum = max(map(a, seq))
    return list(filter(lambda elem: a(elem) == maximum, seq))
environment['maximal'] = maximal


# .n. mathematical constants
def Pnumbers(a):
    if isinstance(a, int) and a < 7:
        return [math.pi,
                math.e,
                2**.5,
                (1 + 5**0.5) / 2,
                float("inf"),
                -float("inf"),
                float("nan")][a]

    if is_lst(a):
        # Algorithm from:
        # http://stackoverflow.com/a/2158532/3739851
        # cc by-sa 3.0
        # Altered to use is_lst
        def flatten(l):
            for el in l:
                if is_lst(el):
                    for sub in flatten(el):
                        yield sub
                else:
                    yield el

        return list(flatten(a))

    return unknown_types(Pnumbers, ".n", a)
environment['Pnumbers'] = Pnumbers


# .O. int/str. Octal, average
def Poct(a):
    if is_col(a) and all(map(is_num, a)):
        if len(a) == 0:
            return 0.0
        else:
            return sum(a) / len(a)
    elif isinstance(a, int) or isinstance(a, str):
        return oct(int(hex_multitype(a, ".O"), 16))[2:]
    return unknown_types(Poct, ".O", a)
environment['Poct'] = Poct


# .p. seq
def permutations(a):
    if is_num(a):
        a = urange(a)
    if not is_col(a):
        return unknown_types(permutations, ".p", a)
    return itertools_norm(itertools.permutations, a, len(a))
environment['permutations'] = permutations


# .P. seq, int
def permutations2(a, b):
    if isinstance(a, int) and isinstance(b, int):
        # compute n P r
        return functools.reduce(operator.mul, range(a - b + 1, a + 1), 1)

    if is_col(a) and isinstance(b, int):
        return itertools_norm(itertools.permutations, a, b)

    if isinstance(a, int) and isinstance(b, str):
        return "".join(permutations2(a, list(b)))

    if isinstance(a, int) and is_col(b):
        # Algorithm modified from
        # http://stackoverflow.com/a/6784359/1938435
        # cc by-sa 3.0
        items = list(b)
        result = []
        a %= math.factorial(len(items))
        for x in range(len(items) - 1, -1, -1):
            fact = math.factorial(x)
            index = a // fact
            a -= index * fact
            result.append(items[index])
            del items[index]
        return result

    return unknown_types(permutations2, ".P", a, b)
environment['permutations2'] = permutations2


# .q. N\A
def Pexit():
    sys.exit(0)
environment['Pexit'] = Pexit


# .Q. N/A
@functools.lru_cache(1)
def eval_all_input():
    return [literal_eval(val) for val in all_input()]
environment['eval_all_input'] = eval_all_input


# .r col, seq
def rotate(a, b):
    if is_col(a) and is_seq(b):
        def trans_func(elem):
            if elem in b:
                elem_index = b.index(elem)
                return b[(elem_index + 1) % len(b)]
            else:
                return elem
        trans_a = map(trans_func, a)
        if isinstance(a, str):
            return ''.join(trans_a)
        if isinstance(a, set):
            return set(trans_a)
        return list(trans_a)

    return unknown_types(rotate, ".r", a, b)
environment['rotate'] = rotate


# .R num, num
def Pround(a, b):
    if is_num(a) and b == 0:
        return int(round(a))
    if is_num(a) and isinstance(b, int):
        return round(a, b)
    if is_num(a) and is_num(b):
        round_len = 0
        while round(b, round_len) != b and round_len < 15:
            round_len += 1
        return round(a, round_len)
    return unknown_types(Pround, ".R", a, b)
environment['Pround'] = Pround


# .s. str, str / seq, any
def Pstrip(a, b):
    if isinstance(a, str) and isinstance(b, str):
        return a.strip(b)
    if is_seq(a):
        if is_col(b):
            strip_items = list(b)
        else:
            strip_items = [b]
        seq = copy.deepcopy(a)
        while seq and seq[0] in strip_items:
            seq.pop(0)
        while seq and seq[-1] in strip_items:
            seq.pop()
        return seq
    return unknown_types(Pstrip, ".s", a, b)
environment['Pstrip'] = Pstrip


# .S. seq, int
def shuffle(a):
    if isinstance(a, list):
        random.shuffle(a)
        return a
    if isinstance(a, str):
        tmp_list = list(a)
        random.shuffle(tmp_list)
        return ''.join(tmp_list)
    if is_col(a):
        tmp_list = list(a)
        random.shuffle(tmp_list)
        return tmp_list
    if is_num(a):
        tmp_list = urange(a)
        random.shuffle(tmp_list)
        return tmp_list

    return unknown_types(shuffle, '.S', a)
environment['shuffle'] = shuffle


# .t. num, int
def trig(a, b=' '):
    if is_num(a) and isinstance(b, int):

        funcs = [math.sin, math.cos, math.tan,
                 math.asin, math.acos, math.atan,
                 math.degrees, math.radians,
                 math.sinh, math.cosh, math.tanh,
                 math.asinh, math.acosh, math.atanh]

        return funcs[b](a)

    if is_lst(a):
        width = max(len(row) for row in a)
        padded_matrix = [list(row) + (width - len(row)) * [b] for row in a]
        transpose = list(zip(*padded_matrix))
        if all(isinstance(row, str) for row in a) and isinstance(b, str):
            normalizer = ''.join
        else:
            normalizer = list
        norm_trans = [normalizer(padded_row) for padded_row in transpose]
        return norm_trans
    return unknown_types(trig, ".t", a, b)
environment['trig'] = trig


# .T. list
def transpose(a):
    if is_col(a):
        if not a:
            return a
        lol = [urange(elem) if is_num(elem) else elem for elem in a]
        cols = max(len(sublist) for sublist in lol)
        trans = [[] for _ in range(cols)]
        for sublist in lol:
            for index, elem in enumerate(sublist):
                trans[index].append(elem)
        if all(isinstance(sublist, str) for sublist in lol):
            return list(map(''.join, trans))
        else:
            return list(map(list, trans))
    return unknown_types(transpose, ".T", a)
environment['transpose'] = transpose


# .u. lambda, seq, any
def cu_reduce(a, b, c=None):
    if c is None:
        counter = 0
        results = [copy.deepcopy(b)]
        acc = a(b, counter)
        while acc not in results:
            counter += 1
            results.append(copy.deepcopy(acc))
            acc = a(acc, counter)
        return results
    if is_seq(b) or is_num(b):
        if is_num(b):
            seq = urange(b)
        else:
            seq = b
        acc = c
        results = [copy.deepcopy(acc)]
        while len(seq) > 0:
            h = seq[0]
            acc = a(acc, h)
            seq = seq[1:]
            results.append(copy.deepcopy(acc))
        return results
environment['cu_reduce'] = cu_reduce


# .U. lambda, seq
def reduce2(a, b):
    if is_seq(b) or isinstance(b, int):
        if is_num(b):
            whole_seq = urange(b)
        else:
            whole_seq = b
        if len(whole_seq) == 0:
            return unknown_types(reduce2, ".U", a, b)

        acc = whole_seq[0]
        seq = whole_seq[1:]

        while len(seq) > 0:
            h = seq[0]
            acc = a(acc, h)
            seq = seq[1:]
        return acc
    return unknown_types(reduce2, ".U", a, b)
environment['reduce2'] = reduce2


# .w. write
def Pwrite(a, b=''):
    if not isinstance(b, str):
        return unknown_types(Pwrite, ".w", a, b)

    if b.startswith("http"):
        if isinstance(a, dict):
            a = "&".join("=".join(i) for i in a.items())
        return [lin[:-1] if lin[-1] == '\n' else lin for lin
                in urllib.request.urlopen(b, a.encode("UTF-8"))]

    prefix = b.split('.')[0] if b else 'o'
    suffix = b.split('.')[1] if '.' in b else None

    if is_lst(a):
        from PIL import Image
        suffix = suffix if suffix else 'png'

        if not is_lst(a[0][0]):
            a = [[(i, i, i) for i in j] for j in a]
        else:
            a = [[tuple(i) for i in j] for j in a]

        header = "RGBA" if len(a[0][0]) > 3 else "RGB"
        img = Image.new(header, (len(a[0]), len(a)))

        img.putdata(Psum(a))
        img.save(prefix + "." + suffix)
    else:
        suffix = suffix if suffix else "txt"

        with open(prefix + '.' + suffix, 'a', encoding='iso-8859-1') as f:
            if is_seq(a) and not isinstance(a, str):
                f.write("\n".join(map(str, a)) + "\n")
            else:
                f.write(str(a) + "\n")

environment['Pwrite'] = Pwrite


# .W lambda, lambda, any
def apply_while(a, b, c):
    condition = a
    function = b
    value = c
    while condition(value):
        value = function(value)
    return value
environment['apply_while'] = apply_while


# .x try except
def Pexcept(a, b):
    try:
        return a()
    except:
        return b()
environment['Pexcept'] = Pexcept


# .y All subsets, all orders
def all_subset_orders(a):
    if is_num(a):
        a = urange(a)
    if not is_col(a):
        return unknown_types(all_subset_orders, ".y", a)
    def all_subsets_all_orders(a):
        return  itertools.chain.from_iterable(itertools.permutations(a, r) for r in range(len(a)+1))
    return itertools_norm(all_subsets_all_orders, a)
environment['all_subset_orders'] = all_subset_orders

# .z. N/A
@functools.lru_cache(1)
def all_input():
    return [l.rstrip("\n") for l in sys.stdin]
environment['all_input'] = all_input


# .Z. string
def compress(a):
    if isinstance(a, str):
        a = a.encode('iso-8859-1')
        try:
            a = zlib.decompress(a)
        except:
            a = zlib.compress(a, 9)
        return a.decode('iso-8859-1')

    return unknown_types(compress, ".Z", a)
environment['compress'] = compress


"""
To encode into this format, use the following Pyth expression:

J"Your string here"++hSJeSJCi-RChSJCMJ-hCeSJChSJ

Basically, subtract the character value of the smallest character from every character,
then base encode in the minimal possible base, convert back to a string, and stick
the smallest two characters at the front.
"""


# .". Special - str
def packed_str(pack):
    if not isinstance(pack, str):
        return unknown_types(packed_str, '."', pack)
    assert len(pack) >= 2, '." needs bounds.'
    lowest = pack[0]
    highest = pack[1]
    offset = ord(lowest)
    base = ord(highest) - ord(lowest) + 1
    int_rep = Pchr(pack[2:])
    reduced = from_base_ten(int_rep, base)
    final = ''.join(chr(a + offset) for a in reduced)
    return final
environment['packed_str'] = packed_str


# .&. int, int
def bitand(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return a & b

    return unknown_types(bitand, ".&", a, b)
environment['bitand'] = bitand


# .|. int, int
def bitor(a, b):
    if isinstance(a, int) and isinstance(b, int):
        return a | b
    if is_col(a) and is_col(b):
        union = set(a) | set(b)
        if is_lst(a):
            return list(union)
        if isinstance(a, str):
            return ''.join(union)
        return union

    return unknown_types(bitor, ".|", a, b)
environment['bitor'] = bitor


# .<. int/seq, int
def leftshift(a, b):
    if not isinstance(b, int):
        return unknown_types(leftshift, ".<", a, b)

    if is_seq(a):
        if not a:
            return a
        b %= len(a)
        return a[b:] + a[:b]

    if isinstance(a, int):
        return a << b

    return unknown_types(leftshift, ".<", a, b)
environment['leftshift'] = leftshift


# .>. int/seq, int
def rightshift(a, b):
    if not isinstance(b, int):
        return unknown_types(rightshift, ".>", a, b)

    if is_seq(a):
        if not a:
            return a
        b %= len(a)
        return a[-b:] + a[:-b]

    if isinstance(a, int):
        return a >> b

    return unknown_types(rightshift, ".>", a, b)
environment['rightshift'] = rightshift


# ./. seq/int
def partition(a):
    if is_seq(a):
        all_splits = []
        for n in range(len(a)):  # 0, 1, ..., len(a)-1 splits
            for idxs in itertools.combinations(range(1, len(a)), n):
                all_splits.append(
                    [a[i:j] for i, j in zip((0,) + idxs, idxs + (None,))])
        return all_splits

    if isinstance(a, int) and a >= 0:
        @memoized
        def integer_partition(number):
            result = set()
            result.add((number, ))
            for x in range(1, number):
                for y in integer_partition(number - x):
                    result.add(tuple(sorted((x, ) + y)))
            return result
        return list(map(list, sorted(integer_partition(a))))

    return unknown_types(partition, "./", a)
environment['partition'] = partition


# ._. int
def sign(a):
    if is_seq(a):
        return [a[:end] for end in range(1, len(a) + 1)]
    if is_num(a):
        if a < 0:
            return -1
        if a > 0:
            return 1
        else:
            return 0
    return unknown_types(sign, "._", a)
environment['sign'] = sign


# .-. seq, seq
def remove(a, b):
    if not is_col(a) or not is_col(b):
        return unknown_types(remove, ".-", a, b)

    seq = list(a)
    to_remove = list(b)
    for elem in to_remove:
        if elem in seq:
            del seq[seq.index(elem)]

    if isinstance(a, str):
        return ''.join(seq)
    return seq
environment['remove'] = remove


# .+. seq
def deltas(a):
    if is_seq(a):
        return [minus(a[i+1], x) for i,x in enumerate(a[:-1])]
    return unknown_types(deltas, ".+", a)
environment['deltas'] = deltas    

# .:, int/seq, int
def substrings(a, b=None):
    if is_seq(a):
        seq = a
    elif is_num(a):
        seq = urange(a)
    else:
        return unknown_types(substrings, ".:", a, b)
    if is_col(b):
        return sum(([seq[start:start + step]
                     for step in b if start + step <= len(seq)]
                    for start in range(len(seq))), [])
    if isinstance(b, int):
        step = b
    elif isinstance(b, float):
        step = int(b * len(seq))
    elif not b:
        all_substrs = [substrings(seq, step)
                       for step in range(1, len(seq) + 1)]
        return list(itertools.chain.from_iterable(all_substrs))
    else:
        return unknown_types(substrings, ".:", a, b)
    return [seq[start:start + step] for start in range(len(seq) - step + 1)]
environment['substrings'] = substrings


# .{. All.
def Pset(a=set()):
    if is_num(a):
        return set([a])
    if is_col(a):
        try:
            return set(a)
        except TypeError:
            return set(map(tuple, a))
    return unknown_types(Pset, ".{", a)
environment['Pset'] = Pset


# .! factorial
def factorial(a):
    if isinstance(a, int):
        return math.factorial(a)
    if is_num(a):
        return math.gamma(a + 1)
    return unknown_types(factorial, '.!', a)
environment['factorial'] = factorial


# .[. str, str, int
def pad(a, b, c):
    if isinstance(a, str) and isinstance(b, str) and isinstance(c, int):
        pad_len = c if len(a) == 0 else (c - len(a)) % c
        return a + (b * pad_len)[:pad_len]
    if isinstance(b, str) and isinstance(c, str) and isinstance(a, int):
        pad_len = a if len(b) == 0 else (a - len(b)) % a
        pad_string = (c * pad_len)[:pad_len]
        return pad_string[:pad_len // 2] + b + pad_string[pad_len // 2:]
    if isinstance(c, str) and isinstance(a, str) and isinstance(b, int):
        pad_len = b if len(c) == 0 else (b - len(c)) % b
        return (a * pad_len)[:pad_len] + c

    if is_seq(a) and isinstance(c, int):
        pad_len = c if len(a) == 0 else (c - len(a)) % c
        return list(a) + [b] * pad_len
    if is_seq(b) and isinstance(a, int):
        pad_len = a if len(b) == 0 else (a - len(b)) % a
        return [c] * (pad_len // 2) + list(b) + [c] * ((pad_len + 1) // 2)
    if is_seq(c) and isinstance(b, int):
        pad_len = b if len(c) == 0 else (b - len(c)) % b
        return [a] * pad_len + list(c)

    return unknown_types(pad, ".[", a, b, c)
environment['pad'] = pad


lambda_f = ('f', 'm', 'o', 'u', '.b', '.e', '.f', '.g', '.I',
            '.m', '.M', '.u', '.U')
end_statement = ('B', 'R', '.*')
variables = 'bdGHkNQTYzZ'

# Variables cheat sheet:
# b = "\n"
# d is for map, d=' '
# G is for reduce, G=string.ascii_lowercase (abc..xyz)
# H is for reduce, H = {}
# k = ''
# J - Autoinitializer - copies, no stringing.
# K - Autoinitializer - can be strung (KJw), no copy.
# N = None, second option variable for map,filter,reduce
# T is for filter, second variable option for reduce, T=10
# Y = []
# Z = 0

c_to_s = {
    'D': ('@memoized\ndef {0}:{1}', 1),
    'D without memoization': ('def {0}:{1}', 1),
    'F': ('for {0} in num_to_range({1}):{2}', 2),
    'I': ('if {0}:{1}', 1),
    'W': ('while {0}:{1}', 1),
    '#': ('while True:\n try:{0}\n except Exception:\n  break', 0, 1),
    '.V': ('for b in infinite_iterator({0}):{1}', 1),
    'else': ('else:{0}', 0),
}

# Arbitrary format operators - use for assignment, infix, etc.
# All surrounding strings, arity
c_to_i = {
    '=': ('assign(\'{0}\',{1})', 2),
    '~': ('post_assign(\'{0}\',{1})', 2),
    '&': ('({0} and {1})', 2),
    '|': ('({0} or {1})', 2),
    '?': ('({1} if {0} else {2})', 3),
    ',': ('[{0},{1}]', 2),
    'B': ('break', 0),
    'J': ('assign("J",{0})', 1),
    'K': ('assign("K",{0})', 1),
    'R': ('return {0}', 1),
    '.W': ('apply_while(lambda H:{0}, lambda Z:{1}, {2})', 3),
    '.x': ('Pexcept(lambda:{0}, lambda:{1})', 2),
    '.*': ('*({0})', 1),
    '.)': ('{0}.pop()', 1),
    '.(': ('{0}.pop({1})', 2),
}

# Simple functions only.
# Extensible is allowed, nothing else complicated is.
# name,arity
c_to_f = {
    '`': ('repr', 1),
    '!': ('Pnot', 1),
    '@': ('lookup', 2),
    '%': ('mod', 2),
    '^': ('Ppow', 2),
    '*': ('times', 2),
    '(': ('Ptuple', float("inf")),
    '-': ('minus', 2),
    '_': ('neg', 1),
    '+': ('plus', 2),
    '[': ('Plist', float("inf")),
    ']': ('singleton', 1),
    '{': ('uniquify', 1),
    '}': ('Pin', 2),
    "'": ('read_file', 1),
    ':': ('at_slice', 3),
    '<': ('lt', 2),
    '>': ('gt', 2),
    '/': ('div', 2),
    ' ': ('', 1),
    '\n': ('imp_print', 1),
    'a': ('append', 2),
    'C': ('Pchr', 1),
    'c': ('chop', 2),
    'E': ('eval_input', 0),
    'e': ('end', 1),
    'f': ('Pfilter', 2),
    'g': ('gte', 2),
    'h': ('head', 1),
    'i': ('base_10', 2),
    'j': ('join', 2),
    'l': ('Plen', 1),
    'm': ('Pmap', 2),
    'n': ('ne', 2),
    'O': ('rchoice', 1),
    'o': ('order', 2),
    'P': ('primes_pop', 1),
    'p': ('Pprint', 1),
    'q': ('equal', 2),
    'r': ('Prange', 2),
    'S': ('Psorted', 1),
    's': ('Psum', 1),
    't': ('tail', 1),
    'U': ('urange', 1),
    'u': ('reduce', 3),
    'v': ('Punsafe_eval', 1),
    'w': ('input', 0),
    'X': ('assign_at', 3),
    'x': ('index', 2),
    'y': ('subsets', 1),
    '.A': ('all', 1),
    '.a': ('Pabs', 1),
    '.B': ('Pbin', 1),
    '.b': ('binary_map', 3),
    '.c': ('combinations', 2),
    '.C': ('combinations_with_replacement', 2),
    '.d': ('dict_or_date', 1),
    '.D': ('divmod_or_delete', 2),
    '.E': ('Pany', 1),
    '.e': ('Penumerate', 2),
    '.f': ('first_n', 3),
    '.F': ('Pformat', 2),
    '.g': ('group_by', 2),
    '.H': ('Phex', 1),
    '.h': ('Phash', 1),
    '.i': ('interleave', 2),
    '.I': ('invert', 2),
    '.j': ('Pcomplex', 2),
    '.l': ('log', 2),
    '.m': ('minimal', 2),
    '.M': ('maximal', 2),
    '.n': ('Pnumbers', 1),
    '.O': ('Poct', 1),
    '.p': ('permutations', 1),
    '.P': ('permutations2', 2),
    '.q': ('Pexit', 0),
    '.Q': ('eval_all_input', 0),
    '.r': ('rotate', 2),
    '.R': ('Pround', 2),
    '.S': ('shuffle', 1),
    '.s': ('Pstrip', 2),
    '.t': ('trig', 2),
    '.T': ('transpose', 1),
    '.U': ('reduce2', 2),
    '.u': ('cu_reduce', 3),
    '.v': ('pyth_eval', 1),
    '.w': ('Pwrite', 2),
    '.y': ('all_subset_orders', 1),
    '.z': ('all_input', 0),
    '.Z': ('compress', 1),
    '."': ('packed_str', 1),
    '.^': ('pow', 3),
    '.&': ('bitand', 2),
    '.|': ('bitor', 2),
    '.<': ('leftshift', 2),
    '.>': ('rightshift', 2),
    './': ('partition', 1),
    '._': ('sign', 1),
    '.-': ('remove', 2),
    '.+': ('deltas', 1),
    '.:': ('substrings', 2),
    '.{': ('Pset', 1),
    '.!': ('factorial', 1),
    '.[': ('pad', 3),
}

optional_final_args = {
    ':': 1,
    'c': 1,
    'f': 1,
    'j': 1,
    'u': 1,
    'X': 1,
    '.b': 1,
    '.f': 1,
    '.j': 2,
    '.l': 1,
    '.u': 1,
    '.w': 1,
    '.:': 1,
    '.{': 1,
    '.t': 1,
}

replacements = {
    'V': [['F', 'N'], ['F', 'H'], ['F', 'b'], ],
    'A': [['=', ',', 'G', 'H'], ],
    'L': [['D', 'y', 'b', 'R'], ['D', "'", 'b', 'R'], ],
    'M': [['D', 'g', 'G', 'H', 'R'], ['D', 'n', 'G', 'H', 'R'], ],
    '.N': [['D', ':', 'N', 'T', 'Y', 'R'], ['D', 'X', 'N', 'T', 'Y', 'R'], ],
    '.?': [[')', 'else'], ],
}

rotate_back_replacements = ('V',)


# Gives next function header to use - for filter, map, reduce.

lambda_vars = {
    'f': ['T', 'Y', 'Z'],
    'm': ['d', 'k', 'b'],
    'o': ['N', 'Z'],
    'u': ['G, H', 'N, T'],
    '.b': ['N, Y'],
    '.e': ['k, b', 'Y, Z'],
    '.f': ['Z'],
    '.g': ['k'],
    '.I': ['G'],
    '.m': ['b'],
    '.M': ['Z'],
    '.u': ['N, Y'],
    '.U': ['b, Z', 'k, Y'],
}

# For autoinitializers. One shot, not rotating.
next_c_to_i = {
    'J': (('J'), 0),
    'K': (('K'), 0),
}

# Prependers.
prepend = {
    'Q': ["=", "Q", "E"],
    'z': ["=", "z", "w"],
}



def lex(code):
    remainder = code
    tokens = []
    while remainder:
        split_point = find_split_point(remainder)
        token, remainder = remainder[:split_point], remainder[split_point:]
        tokens.append(token)
    return tokens

def find_split_point(code):
    if len(code) == 1:
        return 1
    if code[0] == ".":
        if code[1] == '"':
            return string_split(code[1:]) + 1
        if code[1] not in "0123456789":
            return 2
    if code[0] == '\\':
        return 2
    if code[0] in ".123456789":
        return num_split(code)
    if code[0] == '"':
        return string_split(code)
    if code[0] == '$':
        return python_lit_split(code)
    return 1

def string_split(code):
    assert code[0] == '"'
    point = 1
    while point < len(code):
        if code[point] == '\\':
            if len(code) == point + 1:
                point += 1
                break 
            elif code[point+1] in ('"', '\\'):
                point += 2
                continue
        if code[point] == '"':
            point += 1
            break
        else:
            point += 1
    return point

def num_split(code):
    point = 0
    seen_a_dot = False
    while point < len(code) \
          and code[point] in ".0123456789" \
          and (not (seen_a_dot and code[point] == '.')):
        seen_a_dot = seen_a_dot or code[point] == '.'
        point += 1
    if point < len(code) and code[point-1] == '.':
        point -= 1
    return point

def python_lit_split(code):
    assert code[0] == '$'
    if '$' not in code[1:]:
        return len(code)
    else:
        return code[1:].index('$') + 2



sys.setrecursionlimit(100000)

lambda_stack = []
preps_used = set()
state_maintaining_depth = 0

# Parse it!


def general_parse(code, safe_mode):
    # Parsing
    args_list = []
    tokens = lex(code)
    while tokens != []:
        to_print = add_print(tokens)
        parsed, tokens = parse(tokens, safe_mode)
        if to_print:
            parsed = 'imp_print(' + parsed + ')'
        # Finish semicolon parsing
        if tokens and tokens[0] == ';':
            tokens = tokens[1:]
        args_list.append(parsed)
    # Build the output string.
    args_list = add_preps(preps_used, safe_mode) + args_list
    py_code = '\n'.join(args_list)
    return py_code


def parse(tokens, safe_mode, spacing="\n "):
    assert isinstance(tokens, list)
    # If we've reached the end of the string, finish up.
    if not tokens:
        if lambda_stack:
            return lambda_stack[-1], []
        else:
            preps_used.add('Q')
            return 'Q', []
    # Separate active character from the rest of the code.
    active_token = tokens[0]
    rest_tokens = tokens[1:]
    assert isinstance(active_token, str)
    # Deal with numbers
    if active_token == '.':
        raise PythParseError(active_token, rest_tokens)
    if active_token[0] in "0123456789"\
       or active_token[0] == '.' and active_token[1] in "0123456789":
        return active_token, rest_tokens
    # String literals
    if active_token[0] == '"':
        return str_parse_next(active_token), rest_tokens
    if active_token[:2] == '."':
        string = str_parse_next(active_token[1:])
        return "%s(%s)" % (c_to_f['."'][0], string), rest_tokens
    # Python code literals
    if active_token[0] == '$':
        if safe_mode:
            raise UnsafeInputError(active_token, rest_tokens)
        else:
            return active_token.strip('$'), rest_tokens
    # End paren is magic (early-end current function/statement).
    if active_token == ')':
        return '', rest_tokens
    if active_token == ';':
        # Inside a lambda, return the innermost lambdas leading variable.
        if lambda_stack or state_maintaining_depth:
            return 'env_lookup({!r})'.format((lambda_stack or ['Q'])[-1]), rest_tokens
        # Semicolon is more magic (early-end all active functions/statements).
        if not rest_tokens:
            return '', [';']
        else:
            return '', [';'] + rest_tokens
    # Designated variables
    if active_token in variables:
        if active_token in prepend:
            preps_used.add(active_token)
        return active_token, rest_tokens
    if active_token[0] == '\\':
        if active_token[1] in '"\\':
            return '"\\%s"' % active_token[1], rest_tokens
        else:
            return '"%s"' % active_token[1], rest_tokens
    # Replace replaements
    if active_token in replacements:
        return replace_parse(active_token, rest_tokens, safe_mode, spacing)
    # Syntactic sugar handling.
    if rest_tokens and (active_token in c_to_f or active_token in c_to_i):
        sugar_char = rest_tokens[0]
        remainder = rest_tokens[1:]
        if active_token in c_to_f:
            arity = c_to_f[active_token][1]
        else:
            arity = c_to_i[active_token][1]

        # Sugar Chaining
        sugar_chars = 'FMLBRID#VW'
        sugar_active_tokens = [active_token]
        while sugar_char in sugar_chars and remainder and remainder[0] in sugar_chars:
            sugar_active_tokens += sugar_char
            sugar_char = remainder[0]
            remainder = remainder[1:]
        if arity > 0:
            if sugar_char == 'F':
                if arity == 1:
                    # Unary: Repeated application
                    rep_arg1, post1 = parse(remainder, safe_mode)
                    rep_arg2, post2 = parse(post1, safe_mode)
                    func, rest = parse(sugar_active_tokens + ['b'], safe_mode)
                    assert not rest, "Sugar parse F repeat failed"
                    func = "lambda b:" + func
                    return "repeat({}, {}, {})".format(func, rep_arg1, rep_arg2), post2
                if arity == 2:
                    # <binary function/infix>F: Fold operator
                    fold_list, post_fold = next_seg(remainder, safe_mode)
                    if len(sugar_active_tokens) == 1\
                            and sugar_active_tokens[0] in c_to_f\
                            and not sugar_active_tokens[0] in lambda_f:
                        parsed_list, rest = parse(fold_list, safe_mode)
                        assert not rest, "Sugar parse F fold simple failed"
                        func = c_to_f[sugar_active_tokens[0]][0]
                        return "fold({}, {})".format(func, parsed_list), post_fold
                    reduce_arg1 = lambda_vars['.U'][0][0]
                    reduce_arg2 = lambda_vars['.U'][0][-1]
                    full_fold, rest = parse([".U"] + sugar_active_tokens +
                                            [reduce_arg1, reduce_arg2] + fold_list, safe_mode)
                    assert not rest, "Sugar parse F fold failed"
                    return full_fold, post_fold
                if arity > 2:
                    # Just splat it - it's a common use case.
                    splat_list, post_splat = next_seg(remainder, safe_mode)
                    full_splat, rest = parse(sugar_active_tokens + ['.*'] + splat_list, safe_mode)
                    assert not rest, "Sugar parse F splat failed"
                    return full_splat, post_splat

            # <function>M: Map operator
            if sugar_char == 'M':
                m_arg = lambda_vars['m'][0][0]
                if arity == 1:
                    map_target, post_map = next_seg(remainder, safe_mode)
                    full_map, rest = parse(['m'] + sugar_active_tokens + [m_arg] + map_target, safe_mode)
                    assert not rest, "Sugar parse M 1 arg failed"
                    return full_map, post_map
                else:
                    map_target, post_map = next_seg(remainder, safe_mode)
                    full_map, rest = parse(['m'] + sugar_active_tokens + ['F', m_arg] + map_target, safe_mode)
                    assert not rest, "Sugar parse M 2+ args failed"
                    return full_map, post_map

            # <binary function>L<any><seq>: Left Map operator
            # >LG[1 2 3 4 -> 'm>Gd[1 2 3 4'.
            if sugar_char == 'L':
                if arity >= 2:
                    m_arg = lambda_vars['m'][0][0]
                    lmap_lambda_args, remainder = next_n_segs(arity - 1, remainder, safe_mode)
                    lmap_target, post_lmap = next_seg(remainder, safe_mode)
                    full_lmap, rest = parse(['m'] + sugar_active_tokens +
                                            lmap_lambda_args + [m_arg] + lmap_target, safe_mode)
                    assert not rest, "Sugar parse L failed"
                    return full_lmap, post_lmap

            # <function>V<seq><seq> Vectorize operator.
            # Equivalent to <func>MC,<seq><seq>.
            if sugar_char == 'V':
                vmap_target, post_vmap = next_n_segs(2, remainder, safe_mode)
                full_vmap, rest = parse(sugar_active_tokens + ['M', 'C', ','] + vmap_target, safe_mode)
                assert not rest, "Sugar parse V failed"
                return full_vmap, post_vmap

            # <function>W<condition><arg><rgs> Condition application operator.
            # Equivalent to ?<condition><function><arg><args><arg>
            if sugar_char == 'W':
                condition, rest_tokens1 = parse(remainder, safe_mode)
                arg1, _ = state_maintaining_parse(rest_tokens1, safe_mode)
                func, rest_tokens2b = parse(sugar_active_tokens + rest_tokens1, safe_mode)
                return ('(%s if %s else %s)' % (func, condition, arg1), rest_tokens2b)

            # <function>B<arg><args> -> ,<arg><function><arg><args>
            # <unary function>I<any> Invariant operator.
            # Equivalent to q<func><any><any>
            if sugar_char in 'BI':
                dup_dict = {
                    'B': '[{},{}]',
                    'I': '{}=={}',
                }
                dup_format = dup_dict[sugar_char]
                dup_parsed, _ = state_maintaining_parse(remainder, safe_mode)
                non_dup_parsed, post_dup = parse(sugar_active_tokens + remainder, safe_mode)
                return dup_format.format(dup_parsed, non_dup_parsed), post_dup

            # Right operators
            # R is Map operator
            # D is Sort operator
            # # is Filter operator - it looks like a strainer.
            if sugar_char in 'RD#':
                func_dict = {
                    'R': 'm',
                    'D': 'o',
                    '#': 'f',
                }
                func_char = func_dict[sugar_char]
                lambda_arg = lambda_vars[func_char][0][0]
                rop_args, post_rop = next_n_segs(arity, remainder, safe_mode)
                full_rop, rest = parse([func_char] + sugar_active_tokens + [lambda_arg] + rop_args, safe_mode)
                assert not rest, 'Sugar parse %s failed' % sugar_char
                return full_rop, post_rop

    # =<function/infix>, ~<function/infix>: augmented assignment.
    if active_token in ('=', '~'):
        if augment_assignment_test(rest_tokens):
            return augment_assignment_parse(active_token, rest_tokens, safe_mode)

    # And for general functions
    if active_token in c_to_f:
        if active_token in lambda_f:
            return lambda_function_parse(active_token, rest_tokens, safe_mode)
        else:
            return function_parse(active_token, rest_tokens, safe_mode)
    # General format functions/operators
    if active_token in c_to_i:
        return infix_parse(active_token, rest_tokens, safe_mode)
    # Statements:
    if active_token in c_to_s:
        return statement_parse(active_token, rest_tokens, safe_mode, spacing)
    # If we get here, the character has not been implemented.
    # There is no non-ASCII support.
    raise PythParseError(active_token, rest_tokens)


def next_seg(code, safe_mode):
    _, rest = state_maintaining_parse(code, safe_mode)
    pyth_seg = code[:len(code) - len(rest)]
    return pyth_seg, rest


def next_n_segs(n, code, safe_mode):
    if not isinstance(n, int):
        assert n == float('inf'), "arities must be either ints or infinity"
        raise RuntimeError # Can't use unbounded arity function in this context.
    global c_to_i
    global state_maintaining_depth
    saved_c_to_i = c.deepcopy(c_to_i)
    state_maintaining_depth += 1
    remainder = code
    for _ in range(n):
        _, remainder = parse(remainder, safe_mode)
    state_maintaining_depth -= 1
    c_to_i = saved_c_to_i
    return code[:len(code) - len(remainder)], remainder


def state_maintaining_parse(code, safe_mode):
    global c_to_i
    global state_maintaining_depth
    saved_c_to_i = c.deepcopy(c_to_i)
    state_maintaining_depth += 1
    py_code, rest_tokens = parse(code, safe_mode)
    state_maintaining_depth -= 1
    c_to_i = saved_c_to_i
    return py_code, rest_tokens


def augment_assignment_test(rest_tokens):
    func_token = rest_tokens[0]
    return func_token not in variables and func_token not in next_c_to_i and func_token != ','


def augment_assignment_parse(active_token, rest_tokens, safe_mode):
    following_vars = [token for token in rest_tokens if token in variables or token in next_c_to_i]
    var_token = (following_vars + ['Q'])[0]
    return parse([active_token, var_token] + rest_tokens, safe_mode)

def gather_args(active_token, rest_tokens, arity, safe_mode):
    # Recurse until terminated by end paren or EOF
    # or received enough arguments
    args_list = []
    while (len(args_list) != arity
           and not (not rest_tokens
                    and (arity == float('inf')
                         or (active_token in optional_final_args
                             and len(args_list) >= arity - optional_final_args[active_token])))):
        parsed, rest_tokens = parse(rest_tokens, safe_mode)
        if not parsed:
            break
        args_list.append(parsed)
    return args_list, rest_tokens


def lambda_function_parse(active_token, rest_tokens, safe_mode):
    func_name, arity = c_to_f[active_token]
    var = lambda_vars[active_token][0]
    # Swap what variables are used in lambda functions.
    saved_lambda_vars = lambda_vars[active_token]
    lambda_vars[active_token] = lambda_vars[active_token][1:] + [var]
    lambda_stack.append(var[0])
    # Take one argument, the lambda.
    lambda_parsed, rest_tokens = parse(rest_tokens, safe_mode)
    # Rotate back.
    lambda_vars[active_token] = saved_lambda_vars
    lambda_stack.pop()
    partial_args_list, rest_tokens = gather_args(active_token, rest_tokens, arity-1, safe_mode)
    args_list = [lambda_parsed] + partial_args_list
    py_code = '%s(lambda %s:%s)' % (func_name, var, ','.join(args_list))
    return py_code, rest_tokens


def function_parse(active_token, rest_tokens, safe_mode):
    func_name, arity = c_to_f[active_token]
    args_list, rest_tokens = gather_args(active_token, rest_tokens, arity, safe_mode)
    py_code = '%s(%s)' % (func_name, ','.join(args_list))
    return py_code, rest_tokens


def infix_parse(active_token, rest_tokens, safe_mode):
    infixes, arity = c_to_i[active_token]
    args_list = []
    # Lambda infix(es)
    if active_token == '.W':
        lambda_stack.extend(['Z', 'H'])
    while len(args_list) != arity:
        if (not rest_tokens
                and active_token in optional_final_args
                and len(args_list) >= arity - optional_final_args[active_token]):
            args_list.append('')
            break
        parsed, rest_tokens = parse(rest_tokens, safe_mode)
        if not parsed:
            break
        args_list.append(parsed)
        if active_token == '.W' and len(args_list) <= 2:
            lambda_stack.pop()
    # Statements that cannot have anything after them
    if active_token in end_statement:
        rest_tokens = [")"] + rest_tokens
    py_code = infixes.format(*args_list)
    # Advance infixes.
    if active_token in next_c_to_i:
        c_to_i[active_token] = next_c_to_i[active_token]
    return py_code, rest_tokens


def statement_parse(active_token, rest_tokens, safe_mode, spacing):
    # Handle the initial portion (head)
    # addl_spaces denotes the amount of extra spacing needed.
    if len(c_to_s[active_token]) == 2:
        infixes, arity = c_to_s[active_token]
        addl_spaces = ''
    else:
        infixes, arity, num_spaces = c_to_s[active_token]
        addl_spaces = ' ' * num_spaces
    # Handle newlines in infix segments
    infixes = infixes.replace("\n", spacing[:-1])
    args_list, rest_tokens = gather_args(active_token, rest_tokens, arity, safe_mode)
    # Handle the body - ends object as well.
    body_lines = []
    while rest_tokens:
        to_print = add_print(rest_tokens)
        parsed, rest_tokens = parse(rest_tokens, safe_mode, spacing + addl_spaces + ' ')
        if not parsed:
            break
        if to_print:
            parsed = 'imp_print(%s)' % parsed
        body_lines.append(parsed)
    if body_lines == []:
        body_lines = ['pass']
    # Combine pieces - intro, statement, conclusion.
    total_spacing = spacing + addl_spaces
    body = total_spacing + total_spacing.join(body_lines)
    args_list.append(body)
    return infixes.format(*args_list), rest_tokens


def replace_parse(active_token, rest_tokens, safe_mode, spacing):
    # Rotate replacements.
    repl_list = replacements[active_token][0]
    saved_replacements = replacements[active_token]
    replacements[active_token] = replacements[active_token][1:] + [repl_list]
    parsed, remainder = parse(repl_list + rest_tokens, safe_mode, spacing)
    # Rotate back in some cases.
    if active_token in rotate_back_replacements:
        replacements[active_token] = saved_replacements
    return parsed, remainder


# Prependers are magic. Automatically prepend to program if present.
def add_preps(preps, safe_mode):
    return [parse(prepend[var], safe_mode)[0] for var in sorted(preps)]


# Prepend print to any line starting with a function, var or
# safe infix.
def add_print(code):
    if len(code) > 0:
        if code[0] in c_to_s or code[0] in replacements or\
           code[0] in ('=', '~', 'B', 'R', 'p', ' ', '\n', ')', ';'):
            return False
        if code[0] in next_c_to_i:
            return c_to_i[code[0]] == next_c_to_i[code[0]]
        return True


# Pyth eval
def pyth_eval(a):
    if not isinstance(a, str):
        raise BadTypeCombinationError(".v", a)
    return eval(parse(lex(a), True)[0], environment)
environment['pyth_eval'] = pyth_eval


# Preprocessor for multi-line mode.
def preprocess_multiline(code_lines_with_newlines):
    # Reading a file keeps trailing newlines, remove them.
    cleaned_code_lines = [line.rstrip("\n") for line in code_lines_with_newlines]

    # Deal with comments starting with ; and metacommands.
    indent = 2
    i = 0
    end_found = False
    while i < len(cleaned_code_lines):
        code_line = cleaned_code_lines[i].lstrip()
        if code_line.startswith(";"):
            meta_line = code_line[1:].strip()
            cleaned_code_lines.pop(i)

            if meta_line.startswith("indent"):
                try:
                    indent = int(meta_line.split()[1])
                except ValueError:
                    print("Error: expected number after indent meta-command")
                    sys.exit(1)

            elif meta_line.startswith("end"):
                cleaned_code_lines = cleaned_code_lines[:i]
                end_found = True

        elif end_found:
            cleaned_code_lines.pop(i)

        else:
            i += 1

    indent_level = 0
    for linenr, line in enumerate(cleaned_code_lines):
        new_indent_level = 0

        # Deal with indentation.
        for _ in range(indent_level + 1):
            # Allow an increase of at lost one indent level per line.
            if line.startswith("\t"):
                line = line[1:]
            elif line.startswith(" " * indent):
                line = line[indent:]
            else:
                break

            new_indent_level += 1

        # Detect in-line comments.
        in_string = False
        consecutive_spaces = 0
        i = 0
        while i < len(line):
            char = line[i]
            if in_string:
                if char == "\"":
                    in_string = False
                elif char == "\\":
                    i += 1  # Nothing after a backslash can close the string.

            elif char == " ":
                consecutive_spaces += 1
            elif char == "\"":
                consecutive_spaces = 0
                in_string = True
            elif char == "\\":
                consecutive_spaces = 0
                i += 1  # Skip one-character string.
            else:
                consecutive_spaces = 0

            if consecutive_spaces == 2:
                line = line[:i - 1]
                break

            i += 1

        # If this line was non-empty after stripping inline comments, set the
        # new indent level to this line, otherwise keep the old indent level.
        if line.strip():
            indent_level = new_indent_level

        # Strip trailing whitespace, unless the line ends with
        # an uneven amount of backslashes, then
        # keep one trailing whitespace if present.
        stripped_line = line.rstrip()
        if (len(stripped_line) - len(stripped_line.rstrip("\\"))) % 2 == 1:
            stripped_line = line[:len(stripped_line) + 1]

        cleaned_code_lines[linenr] = stripped_line

    return "".join(cleaned_code_lines)


def run_code(code, inp):
    global c_to_i
    global replacements
    global preps_used

    old_stdout, old_stdin = sys.stdout, sys.stdin

    sys.stdout = io.StringIO()
    sys.stdin = io.StringIO(inp)

    error = None

    saved_env = c.deepcopy(environment)
    saved_c_to_i = c.deepcopy(c_to_i)
    saved_replacements = c.deepcopy(replacements)

    preps_used = set()

    try:
        safe_mode_setting = False
        exec(general_parse(code, safe_mode_setting), environment)
    except SystemExit:
        pass
    except Exception as e:
        error = e

    for key in list(environment):
        del environment[key]
    for key in saved_env:
        environment[key] = saved_env[key]
    c_to_i = saved_c_to_i
    replacements = saved_replacements

    result = sys.stdout.getvalue()

    sys.stdout = old_stdout
    sys.stdin = old_stdin

    return result, error

class Repl(cmd.Cmd):
    output = ""
    prompt = ">>> "
    intro = """Welcome to the Pyth REPL.
Each input line will be compiled and executed, and the results of
each one will be passed into the next one's input stream.
"""

    def __init__(self, debug_flag_on):
        self.debug_on = debug_flag_on
        cmd.Cmd.__init__(self)

    def default(self, code):
        global preps_used

        old_stdout, old_stdin = sys.stdout, sys.stdin

        sys.stdout = io.StringIO()
        sys.stdin = io.StringIO(self.output)

        preps_used = set()
        pyth_code_gen = general_parse(code, False)
        if self.debug_on:
            print(pyth_code_gen, file=sys.stderr)
            print('=' * 50, file=sys.stderr)
        try:
            exec(pyth_code_gen, environment)
        except Exception:
            traceback.print_exc()

        self.output = sys.stdout.getvalue()

        sys.stdout = old_stdout
        sys.stdin = old_stdin

        print(self.output, end="")

    def do_EOF(self, line):
        # Shut up, linter
        return True or line or self

    @property
    @memoized
    def docs(self): #Cache the docs so don't read multiple times
        with open("rev-doc.txt") as doc_file:
            docs_dict = {}
            for line in doc_file.read().split("Tokens:\n")[1].split("\n")[:-1]:
                token = (line.split(" ")[0] if not line.startswith(" ") else "space")
                lines = docs_dict.get(token, [])
                lines.append(line)
                docs_dict[token] = lines
            string_docs_dict = {}
            for token, lines in docs_dict.items():
                string_docs_dict[token] = '\n'.join(lines)
            return string_docs_dict

    def do_help(self, line):
        if line:
            print(self.docs.get(line, "%s is not a valid token" % line) if not
                  all(i in "123456789." for i in line) else self.docs["0123456789."])
        else:
            print("""This is the REPL for Pyth, an extremely concise language.
Use "help [token]" to get information about that token, or read rev-doc.txt""")

    def postloop(self):
        print()

    def complete(self):
        pass

if __name__ == '__main__':
    is_interactive = sys.stdin.isatty()
    # Check for command line flags.
    # If debug is on, print code, python code, separator.
    # If help is on, print help message.
    if is_interactive and (("-r" in sys.argv[1:]
                            or "--repl" in sys.argv[1:]) \
                           or all(flag in ("-d", "--debug") for flag in sys.argv[1:])):
        Repl("-d" in sys.argv[1:] or "--debug" in sys.argv[1:]).cmdloop()

    elif len(sys.argv) > 1 and \
            "-h" in sys.argv[1:] \
            or "--help" in sys.argv[1:]:
        print("""This is the Pyth -> Python compliler and executor.
Give file containing Pyth code as final command line argument.

Command line flags:
-c or --code:   Give code as final command arg, instead of file name.
-r or --repl:   Enter REPL mode.
-d or --debug   Show input code, generated python code.
-s or --safe    Run in safe mode. Safe mode does not permit execution of
                arbitrary Python code. Meant for online interpreter.
-l or --line    Run specified runnable line. Runnable lines are those not
                starting with ; or ), and not empty. 0-indexed.
                Specify line with 2nd to last argument. Fails on Windows.
-h or --help    Show this help message.
-m or --multi   Enable multi-line mode.
-M or --no-memoization
                Turn off automatic function memoization.
-D or --only-debug
                Turn off code execution and show only debug informations.
-x    --execute-stdin
                Instead of reading code from file or commandline, use the
                first line of STDIN. Only short-form flags can be used with
                -x, as one argument. (-xcd)
-n    --newline Trim trailing newline from file input.

See opening comment in pyth.py for more info.""")
    else:
        file_or_string = sys.argv[-1]
        if len(sys.argv) == 2 and sys.argv[1][0] == '-':
            flags = sys.argv[1:]
        else:
            flags = sys.argv[1:-1]
        verbose_flags = [flag for flag in flags if flag[:2] == '--']
        short_flags = [flag for flag in flags if flag[:2] != '--']

        def flag_on(short_form, long_form):
            return any(short_form in flag for flag in short_flags) or \
                long_form in verbose_flags
        debug_on = flag_on('d', '--debug')
        code_on = flag_on('c', '--code')
        safe_mode_on = flag_on('s', '--safe')
        line_on = flag_on('l', '--line')
        multiline_on = flag_on('m', '--multiline')
        memo_off = flag_on('M', '--no-memoization')
        only_debug = flag_on('D', '--only-debug')
        execute_stdin = flag_on('x', '--execute-stdin')
        trim_newline = flag_on('n', '--newline')
        if execute_stdin:
            assert len(sys.argv) == 2, "-x is not compatible with multiple command line arguments"
            code_lines = sys.stdin.readlines()
            code_on = False
        if safe_mode_on:
            c_to_f['v'] = ('Pliteral_eval', 1)
            del c_to_f['.w']
        if line_on:
            line_num = int(sys.argv[-2])
        if memo_off:
            c_to_s['D'] = c_to_s['D without memoization']
        if code_on and (line_on or multiline_on):
            print("Error: multiline input from command line.")
        else:
            if code_on:
                pyth_code = file_or_string
            else:
                if not execute_stdin:
                    code_lines = list(open(file_or_string, encoding='iso-8859-1', newline=''))
                if line_on:
                    runable_code_lines = [code_line[:-1]
                                          for code_line in code_lines
                                          if code_line[0] not in ';)\n']
                    pyth_code = runable_code_lines[line_num]
                elif multiline_on:
                    pyth_code = preprocess_multiline(code_lines)
                else:
                    end_marker = '; end\n'
                    if end_marker in code_lines:
                        end_line = code_lines.index(end_marker)
                        pyth_code = ''.join(code_lines[:end_line])
                    else:
                        pyth_code = ''.join(code_lines)
                    if trim_newline and len(pyth_code) > 0 and pyth_code[-1] == '\n':
                        pyth_code = pyth_code[:-1]

            py_code_line = general_parse(pyth_code, safe_mode_on)
            # Debug message
            if debug_on or only_debug:
                print('{:=^50}'.format(' ' + str(len(pyth_code)) + ' chars '),
                      file=sys.stderr)
                print(pyth_code, file=sys.stderr)
                print('=' * 50, file=sys.stderr)
                print(py_code_line, file=sys.stderr)
                print('=' * 50, file=sys.stderr)

            if safe_mode_on and not only_debug:
                # To limit memory use to 200 MB so that it doesn't crash heroku:

                try:
                    import resource
                    resource.setrlimit(resource.RLIMIT_AS, (2*10**8, 2*10**8))
                except:
                    # I think this fails on Windows? In that case I'll just discard the error.
                    pass
                # to fix most security problems, we will disable the use of
                # unnecessary parts of the python
                # language which should never be needed for golfing code.
                # (eg, import statements)

                code_to_remove_tools =\
                    "del __builtins__['__import__']\n"
                # remove import capability
                code_to_remove_tools += "del __builtins__['open']\n"
                # remove capability to read/write to files

                # while this is hardly an exaustive list,
                # and while blacklisting in general
                # should not be used for security, it does
                # solve many security problems.
                exec(code_to_remove_tools + py_code_line, environment)
                # ^ is still evil.

                # Honestly, I'd just whitelist your custom functions
                # and discard anything
                # that doesn't match the whitelist of functions.

                # Anyway, hope you don't mind me patching things up here.
                # Email any questions to

                # PS: Security shouldn't be a black mark to Pyth.
                # I think it's a really neat idea!

            elif not safe_mode_on and not only_debug:
                safe_mode_on = False
                exec(py_code_line, environment)