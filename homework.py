import re
import copy
import string
import time

# =================================================================================================
## Expression Parsing and representation
class Expr:
    """Symbolic representation class of logic expression. The implementation isinstance
    following the AIMA example codes with modifications to serve the purpose of HW3.
    Modifications are:
    1. The equality is modified to perform in context of set rather than list to cover
        the case like 'A | B' is equal to 'B | A'
    2. Accept the "=>" as implication operator
    """

    def __init__(self, op, *args):
        "Op is a string or number; args are Exprs (or are coerced to Exprs)."
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = op  ## YK: In our case, the op is supposed to be string(~,=>,|, &)
        self.args = map(expr, args)  ## Coerce args to Exprs

    def __call__(self, *args):
        """Self must be a symbol with no args, such as Expr('F').  Create a new
        Expr with 'F' as op and the args as arguments."""
        assert is_symbol(self.op) and not self.args
        return Expr(self.op, *args)

    def __repr__(self):
        "Show something like 'P' or 'P(x, y)', or '~P' or '(P | Q | R)'"
        if not self.args:  # Constant or proposition with arity 0
            return str(self.op)
        elif is_symbol(self.op):  # Functional or propositional operator
            return '%s(%s)' % (self.op, ', '.join(map(repr, self.args)))
        elif len(self.args) == 1:  # Prefix operator
            return self.op + repr(self.args[0])
        else:  # Infix operator
            return '(%s)' % (' ' + self.op + ' ').join(map(repr, self.args))

    def __eq__(self, other):
        """x and y are equal iff their ops and args are equal."""
        return (other is self) or (isinstance(other, Expr)
                                   and self.op == other.op and set(self.args) == set(other.args))

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        "Need a hash method so Exprs can live in dicts."
        return hash(self.op) ^ hash(tuple(self.args))

    def __lt__(self, other):
        return Expr('<', self, other)

    def __le__(self, other):
        return Expr('<=', self, other)

    def __ge__(self, other):
        return Expr('>=', self, other)

    def __gt__(self, other):
        return Expr('>', self, other)

    def __add__(self, other):
        return Expr('+', self, other)

    def __sub__(self, other):
        return Expr('-', self, other)

    def __and__(self, other):
        return Expr('&', self, other)

    def __div__(self, other):
        return Expr('/', self, other)

    def __truediv__(self, other):
        return Expr('/', self, other)

    def __invert__(self):
        return Expr('~', self)

    def __lshift__(self, other):
        return Expr('<<', self, other)

    def __rshift__(self, other):
        return Expr('>>', self, other)

    def __mul__(self, other):
        return Expr('*', self, other)

    def __neg__(self):
        return Expr('-', self)

    def __or__(self, other):
        return Expr('|', self, other)

    def __pow__(self, other):
        return Expr('**', self, other)

    def __xor__(self, other):
        return Expr('^', self, other)

    def __mod__(self, other):
        return Expr('<=>', self, other)


def expr(s):
    """Symbol Parser following AIMA example codes
    """
    if isinstance(s, Expr): return s
    if isnumber(s): return Expr(s)
    ## Replace the alternative spellings of operators with canonical spellings
    s = s.replace('=>', '>>').replace('<=', '<<')
    s = s.replace('<=>', '%').replace('=/=', '^')
    ## Replace a symbol or number, such as 'P' with 'Expr("P")'
    s = re.sub(r'([a-zA-Z0-9_.]+)', r'Expr("\1")', s)
    ## Now eval the string.  (A security hole; do not use with an adversary.)
    return eval(s, {'Expr': Expr})


def is_symbol(s):
    "A string s is a symbol if it starts with an alphabetic char."
    return isinstance(s, str) and s[:1].isalpha()


def isnumber(x):
    "Is x a number? We say it is if it has a __int__ method."
    return hasattr(x, '__int__')


def is_variable(s):
    "A logic variable symbol is an initial-lowercase string."
    return is_symbol(s) and s[0].islower()


def is_predic_symbol(s):
    """A proposition logic symbol is an initial-uppercase string other than
    TRUE or FALSE."""
    return is_symbol(s) and s[0].isupper() and s != 'TRUE' and s != 'FALSE'


def extract_variables(s):
    """Extract a set of the variables in sentence s"""
    result = set([])

    def walk(s):
        if is_variable(s.op):
            result.add(s.op)
        else:
            for arg in s.args:
                walk(arg)

    walk(s)
    return result
def extract_constant(s):
    """Extract a set of the variables in sentence s"""
    result = set([])

    def walk(s):
        if is_predic_symbol(s.op) and not s.args:
            result.add(s.op)
        else:
            for arg in s.args:
                walk(arg)
    walk(s)
    return result


## Useful constant Exprs used in examples and code:
TRUE, FALSE, ZERO, ONE, TWO = map(Expr, ['TRUE', 'FALSE', 0, 1, 2])
A, B, C, D, E, F, G, P, Q, x, y, z = map(Expr, 'ABCDEFGPQxyz')

# =================================================================================================
## Global utility functions
def remove_item(item, seq):
    if isinstance(seq, str):
        return seq.replace(item, '')
    else:
        # return [x for x in seq if x != item]
        if isinstance(item, Expr):
            new_seq = copy.deepcopy(seq)
            return filter(lambda a: a != item, new_seq)
        return filter(lambda a: a != item, seq)


def remove_item_sh(item, seq):
    if isinstance(seq, str):
        return seq.replace(item, '')
    else:
        # return [x for x in seq if x != item]
        if isinstance(item, Expr):
            new_seq = seq
            return filter(lambda a: a != item, new_seq)
        return filter(lambda a: a != item, seq)


def remove_dup(seq):
    return list(set(seq))





def find_if(predicate, seq):
    for x in seq:
        if predicate(x): return x
    return None








# =================================================================================================
# Input query utility function
def to_cnf(s):
    """Translate the sentence into CNF form. Following AIMA BOOK 
    """
    if isinstance(s, str): s = expr(s)
    s = eliminate_implications(s)  
    s = move_not_inwards(s)  
    return distribute_and_over_or(s) 


def eliminate_implications(s):
    if not s.args or is_symbol(s.op): return s  ## (Atoms are unchanged.)
    args = map(eliminate_implications, s.args)
    a, b = args[0], args[-1]
    if s.op == '>>':
        return (b | ~a)
    elif s.op == '<<':
        return (a | ~b)
    elif s.op == '<=>':
        return (a | ~b) & (b | ~a)
    elif s.op == '^':
        assert len(args) == 2  ## TODO: relax this restriction
        return (a & ~b) | (~a & b)
    else:
        assert s.op in ('&', '|', '~')
        return Expr(s.op, *args)


def eliminate_implications_user(s):
    if not s.args and is_symbol(s.op): return s
    args_list = []
    for each in s.args:
        args_list.append(eliminate_implications_user(each))


def move_not_inwards(s):
    if s.op == '~':
        NOT = lambda b: move_not_inwards(~b)
        a = s.args[0]
        if a.op == '~': return move_not_inwards(a.args[0])  # ~~A ==> A
        if a.op == '&': return associate('|', map(NOT, a.args))
        if a.op == '|': return associate('&', map(NOT, a.args))
        return s
    elif is_symbol(s.op) or not s.args:
        return s
    else:
        return Expr(s.op, *map(move_not_inwards, s.args))


def distribute_and_over_or(s):
    if s.op == '|':
        s = associate('|', s.args)
        if s.op != '|':
            return distribute_and_over_or(s)
        if len(s.args) == 0:
            return FALSE
        if len(s.args) == 1:
            return distribute_and_over_or(s.args[0])
        conj = find_if((lambda d: d.op == '&'), s.args)
        if not conj:
            return s
        others = [a for a in s.args if a is not conj]
        rest = associate('|', others)
        return associate('&', [distribute_and_over_or(c | rest)
                               for c in conj.args])
    elif s.op == '&':
        return associate('&', map(distribute_and_over_or, s.args))
    else:
        return s


def associate(op, args):
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)


_op_identity = {'&': TRUE, '|': FALSE, '+': ZERO, '*': ONE}
def cnf_to_sentence_list(s):
    assert isinstance(s, Expr)
    if not s.op == '&':
        return [s]
    else:
        return s.args


def dissociate(op, args):
    result = []
    def collect(subargs):
        for arg in subargs:
            if arg.op == op:
                collect(arg.args)
            else:
                result.append(arg)

    collect(args)
    return result





def disjuncts(s):
    """Return a list of the disjuncts in the sentence s.
    >>> disjuncts(A | B)
    [A, B]
    >>> disjuncts(A & B)
    [(A & B)]
    """
    return dissociate('|', [s])


# _________________________________________________________________________________________________
## Construction Knowledge base class
class KB:
    """A simplified knowledge base that is able to give
    only binary answers. Adding sentence by call to tell()
    and ask query by call to ask. Return True if entailed,
    false otherwise. Sentence stored in CNF form. Likewise for
    sentence argument in all subsequent functions.
    """

    def __init__(self, sentence_list=None):
        """ Construction method. Accept only the
        CNF sentences. Be sure to preprocess the
        sentence in the list to CNF.
        """
        self.klist = {}  ## Table-based indexing strategy
        #self.klist_normal = []
        self.newlist = []  ## Newly added clauses
        self.alphabet = list(string.ascii_lowercase)
        self.constantlist = {}
        self.KB_num = 0
        self.risk = 0
        if sentence_list == None:
            return
        for each in sentence_list:  ## In CNF form
            self.tell(each)

    def tell(self, string):
        """Extract all the predicates and create index for them"""
        string_cnf = to_cnf(expr(string))
        sentence_list = cnf_to_sentence_list(string_cnf)
        ## TODO:Standardization

        for sentence in sentence_list:
            sentence = self.factoring(sentence)
            #self.klist_normal.append(sentence)
            self.KB_num += 1
            predicates_list = self.extract_predicates(sentence)
            constant_list = list(extract_constant(sentence))
            for each in predicates_list:
                if self.klist.has_key(each):
                    self.klist[each].append(sentence)
                else:
                    self.klist[each] = [sentence]
            for each in constant_list:
                if self.constantlist.has_key(each):
                    continue
                else:
                    self.constantlist[each] = 1

            

    def check_dup(self, sentence):
        """Check if the CNF sentence is already in the KB"""
        assert isinstance(sentence, Expr)
        check_list = []
        if sentence.op == "~":
            if is_predic_symbol(sentence.args[0].op):
                if self.klist.has_key(sentence.args[0].op):
                    check_list = self.klist[sentence.args[0].op]
        elif is_predic_symbol(sentence.op):
            if is_predic_symbol(sentence.op):
                if self.klist.has_key(sentence.op):
                    check_list = self.klist[sentence.op]
        else:
            for each in sentence.args:
                if is_predic_symbol(each.op):
                    if self.klist.has_key(each.op):
                        check_list = self.klist[each.op]
                        break
        for each in check_list:
            if sentence == each: return True
        return False

    def check_dup_list(self, sentence, sentence_list):
        """Check if the CNF sentence is already in the list"""
        assert isinstance(sentence, Expr)
        for each in sentence_list:
            if each == sentence:
                return True
        return False

    def clear_workkb(self):
        self.newlist = []

    def extract_predicates(self, sentence):
        """Add the sentence to the KB."""
        if not isinstance(sentence, Expr):
            return []
        elif sentence.op == "~" and is_predic_symbol(sentence.args[0].op):
            return ["~" + sentence.args[0].op]
        elif is_predic_symbol(sentence.op):
            return [sentence.op]
        else:
            return list(set(symbol for arg in sentence.args
                            for symbol in self.extract_predicates(arg)))

    def ask(self, query):
        """Return True if entailed, false otherwise. Could be extended to
        return matched knowledge in future"""
        return self.is_entailed(query)

    def unify(self, s_1, s_2, subst):
        """Return the unifier(dictionary) for clause s_1 and s_2.
        Return False when fails. Note: s_1 is a clause(predicate)"""
        if subst.has_key('false'):
            return subst
        if s_1 == s_2:  ##Overloaded equal, op and args
            return subst
        elif is_variable(s_1):
            return self.unify_var(s_1, s_2, subst)
        elif is_variable(s_2):
            return self.unify_var(s_2, s_1, subst)
        elif isinstance(s_1, Expr) and isinstance(s_2, Expr):
            return self.unify(s_1.args, s_2.args, self.unify(s_1.op, s_2.op, subst))
        elif isinstance(s_1, list) and isinstance(s_2, list):
            return self.unify(s_1[1:], s_2[1:], self.unify(s_1[0], s_2[0], subst))
        else:
            subst['false'] = 1
            return subst

    def unify_var(self, var_1, s_2, subst):
        """Return the substitution for a variable against a val/variable"""
        if subst.has_key(var_1):
            return self.unify(subst[var_1], s_2, subst)
        elif subst.has_key(s_2):
            return self.unify(var_1, subst[s_2], subst)
        else:  ## No nested Predicate, no need for occurence check
            subst[var_1] = s_2
            return subst

    def is_entailed(self, query):
        """Return True if entailed otherwise False"""
        #return self.resolution_support(query)
        #self.risk = 0
        query_constant_list = extract_constant(query)
        for each in query_constant_list:
            if not self.constantlist.has_key(each):
                self.risk = 1
                #return False
        return self.resolution_linear(query)

    def resolution(self, query):
        """Resolution inference given the query is
        a single literal"""
        pass

    def resolution_linear(self, query):
        """Linear resolution inference given the query is
        a single literal"""
        # Add the ~query in the self.newklist
        assert isinstance(query, Expr)
        index = 1
        path = []
        if query.op == "~":  ##Prefix operator ~
            self.newlist.append(query.args[0])
            result = self.DFS_resolution(query.args[0], path, index)
        else:
            self.newlist.append(~query)  ## add to the working KB
            result = self.DFS_resolution(~query, path, index)

        if result:
            print path
        return result

    def DFS_resolution(self, goal_sentence, path, index):
        """Branch on sentence or literal ? Seems should branch on sentence"""
        #print index, '\n'
        #if index%10 == 0:
        #    print index
        branch_sentences = []
        if index > 0:
            path_len = len(path[:index-1])
            if path_len > 0:
                for i in xrange(path_len - 1):
                    if path[path_len - 1] == path[i] or path[path_len - 1] == self.newlist[0]:  # root node:
                        return False
        if goal_sentence.op == 'FALSE':
            return True
        #if index > max(2*self.KB_num, 50) and self.risk == 0:
        #    return False
        #if index > max(2*self.KB_num, 30) and self.risk == 1:
        #    return False
        else:
            flag = 1
            if goal_sentence.op == "~":
                if self.klist.has_key(goal_sentence.args[0].op):
                    branch_sentences = self.klist[goal_sentence.args[0].op]
            elif is_predic_symbol(goal_sentence.op):
                if self.klist.has_key('~'+goal_sentence.op):
                    branch_sentences = self.klist['~' + goal_sentence.op]
            else:
                for literal in goal_sentence.args:
                    if literal.op == "~":
                        if self.klist.has_key(literal.args[0].op):
                            branch_sentences = self.klist[literal.args[0].op]
                            break
                if not branch_sentences:
                    if self.klist.has_key("~" + goal_sentence.args[0].op):
                        branch_sentences = self.klist["~" + goal_sentence.args[0].op]
            branch_sentences += self.newlist[:index]
            result = False
            for s in branch_sentences:
                resolvents = self.resolve(goal_sentence, s)
                if not resolvents:
                    continue
                resolvents[0] = self.factoring(resolvents[0])
                flag = 0
                if len(self.newlist) >= index + 1:  # Not the first branch being explored
                    self.newlist[index] = resolvents[0]  # only pick one sentence
                else:
                    self.newlist.append(resolvents[0])  # the first branch being explored
                if len(path) > index:  # Not the first branch being explored
                    path[index] = resolvents[0]  # only pick one sentence
                else:
                    path.append(resolvents[0])  # the first branch being explored
                result = self.DFS_resolution(resolvents[0], path, index + 1)
                if result == True:
                    return True
            if result == False or flag == 1:
                return False  # the goal sentence can not resolve with any setence in the KB and ancestors


                # TODO: Should you hash the newlist as well for picking up relevant sentence quickly ?
                # if keep a hash for newlist, it is extremely difficult to maintain dynamically

    def resolve(self, s_1, s_2):
        """Given two sentences, return a list of new sentences
        resolved. Return ['false'] if s1 and s2 can't be resolved
        new_sentence will contain empty clause if any contradiction
        """
        assert self.standardize_pair(s_1, s_2)
        s_1_list = disjuncts(s_1)
        s_2_list = disjuncts(s_2)
        # Perform standarization
        new_sentence = []
        for s_i in s_1_list:
            target = move_not_inwards(~s_i)
            for s_j in s_2_list:
                subst = {}
                self.unify(target, s_j, subst)
                if not subst.has_key('false'):
                    flag = 1
                    new_s1_list = remove_item(s_i, s_1_list[:])
                    new_s2_list = remove_item(s_j, s_2_list[:])
                    self.subst_predict_list(new_s1_list, subst)
                    self.subst_predict_list(new_s2_list, subst)
                    new_sentence.append(associate('|', remove_dup(new_s1_list + new_s2_list)))
        return new_sentence

    def subst_predict_list(self, disjunct_list, subst):
        for each in disjunct_list:
            if each.op == "~":
                for i in xrange(len(each.args[0].args)):
                    if subst.has_key(each.args[0].args[i].op):
                        each.args[0].args[i].op = subst[each.args[0].args[i].op]
            else:
                for i in xrange(len(each.args)):
                    if subst.has_key(each.args[i].op):
                        each.args[i].op = subst[each.args[i].op]

    def standardize_pair(self, s1, s2):
        """Make all the variables of s2 is different from s1"""
        ##Get all the variables used in s1
        used_letters = {}
        mapping_letter = {}
        letter_set_1 = extract_variables(s1)
        letter_set_2 = extract_variables(s2)
        if letter_set_1.intersection(letter_set_2):
            letter_list = list(letter_set_1)
            for each in letter_list:
                used_letters[each] = 1
            return self.standardize(s2, used_letters, mapping_letter)
        else:
            return True

    def standardize(self, s, used_letters, mapping_letters):
        flag = True
        if is_variable(s.op):
            return self.change_letters(s, used_letters, mapping_letters)
        else:
            for arg in s.args:
                flag &= self.standardize(arg, used_letters, mapping_letters)
            return flag

    def change_letters(self, s, used_letters, mapping_letters):
        """Change the letter for s and add it to a mapping table"""
        if is_variable(s.op):
            temp = s.op
            if mapping_letters.has_key(s.op):
                s.op = mapping_letters[s.op]
                return True
            for each in self.alphabet:
                s.op = each
                if not used_letters.has_key(s.op):
                    used_letters[s.op] = 1
                    mapping_letters[temp] = s.op
                    return True
            return False

    def factoring_core(self, s1):
        assert isinstance(s1, Expr)
        s_len = len(s1.args)
        if s1.op == "~" or is_predic_symbol(s1.op):
            return [s1, 'false']
        else:
            s1_list = disjuncts(s1)
            for i in xrange(s_len):
                target = s1_list[i]
                for j in xrange(i + 1, s_len):
                    s_j = s1_list[j]
                    subst = {}
                    self.unify(target, s_j, subst)
                    if not subst.has_key('false'):
                        new_s1_list = remove_item(target, s1_list)
                        self.subst_predict_list(new_s1_list, subst)
                        new_s1 = associate('|', remove_dup(new_s1_list))
                        return [new_s1, 'true']
            return [s1, 'false']

    def factoring(self, s1):
        new_s1, flag = self.factoring_core(s1)
        while flag == 'true':
            new_s1, flag = self.factoring_core(new_s1)
        s1 = new_s1
        return s1




#========================Main body===================================
start_time = time.time()
FILE_NAME = 'input.txt'
#print 'hello world'
try:
    fp = open(FILE_NAME, 'r')

except IOError, e:
    print "File can not be open\n", e
#----------------Input file parsing-------------------------
#Input file format:
#<N>
#<Queries>
#<M>
#<Sentence>
line_ID = 1
queries_list = []
myKB = KB()
for eachline in fp:
    eachline = eachline.strip('\n')
    if line_ID == 1:
        num_query = int(eachline)
    elif line_ID > 1 and line_ID < num_query+2:
        queries_list.append(eachline)
    elif line_ID is num_query+2:
        num_sentence = int(eachline)
    else:
        myKB.tell(eachline)
    line_ID += 1
fp.close()

FILE_NAME = 'output.txt'
#print 'hello world'
try:
    fp = open(FILE_NAME, 'w')

except IOError, e:
    print "File can not be open\n", e
for each in queries_list:
    if myKB.ask(expr(each)):
        fp.write("TRUE\n")
    else:
        fp.write("FALSE\n")
fp.close()
print("--- %s seconds ---" % (time.time() - start_time))
