import itertools
import re
import sys
gen = itertools.count(1)

# Lambda expression is a tree with 4 possible nodes:
# - Lambda
# - Apply - apply function to expression
# - Var - variable (identifier) in expression, like x. In Lambda calculus it can be some function or value holder
# - Val - value: float, int, string
class Lambda:
  "Lambda node in AST"
  def __init__(self, var, body):
    self.var = var
    self.body = body
  
  def copy(self):
    "Create a copy of node and its descedants"
    return Lambda(self.var, self.body.copy())

  def __repr__(self):
    return '@%s %s' % (self.var, self.body)

  def __eq__(self, other):
    if not isinstance(other, Lambda):
      return False 
    unique_arg = Var(f'x{next(gen)}')
    return self.body.subst(self.var, unique_arg) == other.body.subst(other.var, unique_arg)

  def subst(self, var, expr):
    if var==self.var:
      return self
    else:
      new_body = self.body.subst(var, expr)
      return Lambda(self.var, new_body)

  def beta_step(self):
    return Lambda(self.var, self.body.beta_step())


class Apply:
  def __init__(self, fun, expr):
    self.fun = fun
    self.expr = expr

  def copy(self):
    return Apply(self.fun.copy(), self.expr.copy())

  def __repr__(self):
    def inst_in(e, types):
      return any(map(lambda t: isinstance(e, t), types))
    first = f'({self.fun})' if inst_in(self.fun, [Lambda]) else self.fun
    second = f'({self.expr})' if not inst_in(self.expr, [Var, Val]) else self.expr
    return '%s %s' % (first, second)

  def __eq__(self, other):
    return isinstance(other, Apply) and self.fun==other.fun and self.expr==other.expr

  def beta_redex(self):
    #if isinstance(self.fun, Lambda):
    return self.fun.body.subst(self.fun.var, self.expr)

  def beta_step(self):
    if isinstance(self.fun, Lambda):
      return self.beta_redex()
    else:
      new_fun = self.fun.beta_step()
      if self.fun == new_fun:
        new_expr = self.expr.beta_step()
      else:
        new_expr = self.expr.copy()
      return Apply(new_fun, new_expr)

  def subst(self, var, expr):
    new_fun = self.fun.subst(var, expr)
    new_expr = self.expr.subst(var, expr)
    return Apply(new_fun, new_expr)


class Val:
  def __init__(self, value):
    self.value = value

  def copy(self):
    return Val(self.value)

  def __repr__(self):
    if isinstance(self.value, str):
      return '"'+self.value.replace('"', '\\"')+'"'
    else:
      return str(self.value)

  def __eq__(self, other):
    return isinstance(other, Val) and self.value == other.value

  def subst(self, var, expr):
    return self

  def beta_step(self):
    return self.copy()


class Var:
  def __init__(self, name):
    self.name = name

  def copy(self):
    return Var(self.name)

  def __repr__(self):
    return self.name

  def __eq__(self, other):
    return isinstance(other, Var) and self.name == other.name

  def subst(self, var, expr):
    if self.name==var:
      return expr.copy()
    else:
      return self.copy()

  def beta_step(self):
    return self.copy()


def beta_left(term):
  #print(term)
  term_next = term.beta_step()
  while term != term_next:
    #print(term_next)
    term = term_next
    term_next = term.beta_step()
  return term_next


class Let:
  def __init__(self, var, expr):
    self.var = var
    self.expr = expr


SYM = '\-\+\!\#\$\%\^\&\*\?\,\/\[\]\='
IDENT = f'[a-zA-Z_{SYM}][a-zA-Z0-9_{SYM}]*'
TOKENS = {
  '(': '\(',
  ')': '\)',
  '.': '\.',
  "let": "\:"+IDENT,
  'lambda': '@'+IDENT,
  'number': '(\-|\+)?[0-9]+(\.[0-9]+)?(E(\-|\+)?[0-9]+)?',
  'string': '(\"[^\"]\")',
  'var': IDENT
}


class ApplyAccumulator:
  "Accumulate Applys"
  def __init__(self):
    self.acc = None

  def add(self, term):
    self.acc = Apply(self.acc, term) if self.acc else term


class Parser:
  def parse(self, s):
    self.s = s
    self.pos = 1
    self.scan()
    res = self.parse_statements()
    if self.token:
      self.error("EOF expected")
    return res   

  def scan(self):
    found = re.match('\s+', self.s)
    if found:
      self.s = self.s[len(found.group()):]
    self.token = None
    if not self.s:
      return
    for key, r in TOKENS.items():
      found = re.match(r, self.s)
      if found:
        self.token = key
        self.word = found.group()
        self.pos = self.pos+len(self.word)
        self.s = self.s[len(self.word):]
        return
    raise Exception(f'Invalid token at %d near "%s"' % (self.pos, self.s[:20]))

  def error(self, msg):
    raise Exception(f'({self.pos}): {msg}')

  def parse_statements(self):
    res = []
    while self.token:
      if self.token=='let':
        ident = self.word[1:]
        self.scan()
        if self.token!='var' or self.word!='=':
          self.error('= expected')
        self.scan()
        res.append( Let(ident, self.parse_expr()) )
      else:
        res.append( self.parse_expr() )
      if self.token!='.':
        self.error("'.' expected")
      self.scan()
    return res

  def parse_expr(self):
    res = ApplyAccumulator()
    while self.token and self.token!='.' and self.token!=')':
      if self.token=='(':
        self.scan()
        res.add(self.parse_expr())
        if self.token!=')':
          self.error(') expected')
        self.scan()
      elif self.token=='lambda':
        res.add(self.parse_lambda())
      elif self.token=='var':
        res.add(Var(self.word))
        self.scan()
      elif self.token=='string':
        s = self.word[1:-1].replace('\"', '"')
        res.add(Val(s))
        self.scan()
      elif self.token=='number':
        s = self.word
        v = float(s) if s.find('E')>-1 or s.find('.')>0 else int(s) 
        res.add(Val(v))
        self.scan()
      else:
        self.error('Unexpected token')
    return res.acc

  def parse_lambda(self):
    ll = []
    while self.token=='lambda':
      ll.append(self.word[1:])
      self.scan()
    res = self.parse_expr()
    for l in reversed(ll):
      res = Lambda(l, res)
    return res


parser = Parser()
known = {}

lib = """:I = @x x.
:B = @x @y @z x (y z).
:C = @x @y @z x z y.
:S = @x @y @z x z (y z).
:K = @x @y x.
:T = @x @y x.
:F = @x @y y.
:Y = @f (@g f (g g))(@g f (g g)).
:OMEGA = (@x x x)(@x x x).
"""
# lib = ":x1 = @a @b @c / (- (- 0 b) (sqrt (- (* b b) (* * 4 a c)))) (* 2 a)."

def process_term(term):
  for key, val in known.items():
    term = Apply( Lambda(key, term), val).beta_step()
  return beta_left(term)

def process_statement(s):
  try:
    terms = parser.parse(s)
    for term in terms:
      if isinstance(term, Let):
        term.expr = process_term(term.expr)
        known[term.var] = term.expr
      else:
        print(process_term(term), '.')
  except Exception as e:
    print(e)

def repl():
  print('Welcome to LambdaToy REPL')
  print('(c) Eugene Manaev 2021')
  while True:
    s = input('> ')
    process_statement(s)

process_statement(lib)
if len(sys.argv)==1:
  repl()
with open(sys.argv[1]) as f:
  s = f.read()
  process_statement(s)

