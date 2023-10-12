
from z3 import *
class FormulaFinder():

    template = "undefined"
    cells = 2


    def gen_points(mins, maxs):
        assert(len(mins) == len(maxs))
        if len(mins) == 0:
            return [[]]
        points = []
        min, max = mins[0], maxs[0]
        rec = FormulaFinder.gen_points(mins[1:], maxs[1:])
        for r in rec:
            for m in range(min, max+1):
                points.append([m] + r)

        return points


    def op_addition(op1, op2):
        return Int(op1) + Int(op2)

    def op_and(op1, op2):
        return And(Bool(op1), Bool(op2))

    def op_or(op1, op2):
        return Or(Bool(op1), Bool(op2))



    def op_subtraction(op1, op2):
        return Int(op1) - Int(op2)

    def op_remainder(op1, op2):
        return Int(op1) % Int(op2)

    def rel_equality(op1, op2):
        return Int(op1) == Int(op2)

    def rel_leq(op1, op2):
        return Int(op1) <= Int(op2)

    # |+,-,*,rem,if| = 4
    OPS = 3
    def add_node(s, name, child1, child2, pairs):
        node_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= Int(name))
        s.add(Int(name) <= FormulaFinder.OPS-1)

        ops = [(0, FormulaFinder.op_addition), (1, FormulaFinder.op_subtraction)]
        div_ops = [(2, FormulaFinder.op_remainder)]

        for (opcode, op) in ops:
            lhs = Int(name) == opcode
            rhs = And([Int(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)) for i in range(pairs)])
            s.add(Implies(lhs, rhs))

        for (opcode, op) in div_ops:
            lhs = Int(name) == opcode
            rhs = And([And(Int(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)), Int(child1 + "val_" + str(i)) > 0, Int(child2 + "val_" + str(i)) > 0) for i in range(pairs)])
            s.add(Implies(lhs, rhs))


    # |And, Or| = 2
    BOOL_OPS = 2
    def add_node_bool(s, name, child1, child2, pairs):
        node_vals = [Bool(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= Int(name))
        s.add(Int(name) <= FormulaFinder.BOOL_OPS - 1)
        ops = [(0, FormulaFinder.op_and), (1, FormulaFinder.op_or)]

        for (opcode, op) in ops:
            lhs = Int(name) == opcode
            rhs = And([Bool(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)) for i in range(pairs)])
            s.add(Implies(lhs, rhs))




    # |=,<=| = 2
    RELS = 1
    def add_node_rel(s, name, child1, child2, pairs):
        node_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= Int(name))
        s.add(Int(name) <= FormulaFinder.RELS-1)

        rels = [(0, FormulaFinder.rel_equality), (1, FormulaFinder.rel_leq)]
        #div_ops = [(4, op_remainder)]

        for (opcode, op) in rels:
            lhs = Int(name) == opcode
            rhs = And([Bool(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)) for i in range(pairs)])
            s.add(Implies(lhs, rhs))




    # |input, const| = 2
    LEAFS = 2
    def add_leaf(s, name, dim, pairs):
        leaf = Int(name)
        leaf_const = Int(name + "const")
        leaf_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= leaf)
        s.add(leaf <= dim)
        ### INPUT
        disjunction = []
        for d in range(dim):
            disjunction.append(Implies(Int(name) == d, And([Int(name + "val_" + str(i)) == Int("input_" + str(i) + "_" + str(d)) for i in range(pairs)])))
        s.add(And(disjunction))
        ### CONST
        s.add(Implies(Int(name) == dim, And([Int(name + "val_" + str(i)) == Int(name + "const") for i in range(pairs)])))

    def add_leaf_cross(s, name, cells, pairs):
        leaf = Int(name)
        leaf_vals = [Bool(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= leaf)
        s.add(leaf < cells*3) # X, O, E
        conjunction = []
        for c in range (cells):
            conjunction.append(Implies(Int(name) == c, And([Bool(name + "val_" + str(i)) == (Int("input_" + str(i) + "_" + str(c)) == 0) for i in range(pairs)])))
        for c2 in range (cells):
            c = c2+cells
            conjunction.append(Implies(Int(name) == c, And([Bool(name + "val_" + str(i)) == (Int("input_" + str(i) + "_" + str(c2)) == 1) for i in range(pairs)])))
        for c3 in range (cells):
            c = c3+cells+cells
            conjunction.append(Implies(Int(name) == c, And([Bool(name + "val_" + str(i)) == (Int("input_" + str(i) + "_" + str(c3)) == 2) for i in range(pairs)])))


        s.add(And(conjunction))



    def add_output(s, name, inout):
        outs = list(map(lambda x : x[1], inout))
        for idx, out in enumerate(outs):
            if len(out) >= 1:
                s.add(Or([Int(name + "val_" + str(idx)) == Int("output_" + str(idx) + "_" + str(jdx)) for jdx in range(len(out))]))

    def add_bool_output(s, name, count):
        for i in range(count):
            s.add(Bool(name + "val_" + str(i)) == Bool("output_" + str(i)))


    def print_nim(formula, dim):
        if not formula:
            return "n/a"

        def leaf2str(leaf, leafconst):
            if int(str(leaf)) < dim:
                return "x_" + str(leaf)
            elif int(str(leaf)) == dim:
                return str(leafconst)
            else:
                raise Exception("Strange leaf value:", leaf)

        def op2str(node):
            if node == 0:
                return '+'
            if node == 1:
                return '-'
            if node == 2:
                return '%'

        def rel2str(node):
            if node == 0:
                return '=='
            if node == 1:
                return '<='
            if node == 2:
                return '%'



    def print_tictactoe(formula):
        if not formula:
            return "n/a"

        def leaf2str(z3leaf):
            leaf = int(str(z3leaf))
            if int(leaf) < FormulaFinder.cells:
                return "E(" + str(leaf) + ")"
            elif leaf < FormulaFinder.cells*2:
                return "x(" + str(leaf-FormulaFinder.cells) + ")"
            else:
                return "o(" + str(leaf-FormulaFinder.cells-FormulaFinder.cells) + ")"

        def op2str(node):
            if node == 0:
                return '&&'
            if node == 1:
                return '||'

        l1str = leaf2str(formula['l1'])
        l2str = leaf2str(formula['l2'])
        l3str = leaf2str(formula['l4'])
        l4str = leaf2str(formula['l4'])
        n1str = op2str(formula['n1'])
        n2str = op2str(formula['n2'])
        rootstr = op2str(formula['root'])
        return "(" + l1str + " " + n1str + " " + l2str + ") " + rootstr + " (" + l3str + " " + n2str + " " + l4str + ")"


    def print_boolean(formula, dim):
        if FormulaFinder.template == "nim":
            return FormulaFinder.print_nim(formula, dim)
        elif FormulaFinder.template == "tictactoe":
            return FormulaFinder.print_tictactoe(formula)

    def find_boolean(template, points, mins, maxs, timeout=5000):
        s = Solver()
        s.set("timeout", timeout)
        inputs = []
        outputs = []
        pairs = 0
        dim = len(points[0])
        idx = 0
        for point in FormulaFinder.gen_points(mins, maxs):
                new_inputs = []
                for d in range(dim):
                    new_inputs.append(Int("input_" + str(idx) + "_" + str(d)))
                inputs.append(new_inputs)
                for d in range(dim):
                    s.add(new_inputs[d] == point[d])
                os = []
                const = []
                new_output = Bool("output_" + str(idx))
                pairs += 1
                idx += 1
                if point in points:
                    s.add(new_output)
                else:
                    s.add(Not(new_output))


        interest = []
        if template == "nim":
            FormulaFinder.add_leaf(s, "l1", dim, pairs)
            FormulaFinder.add_leaf(s, "l2", dim, pairs)
            FormulaFinder.add_leaf(s, "l3", dim, pairs)
            FormulaFinder.add_node(s, "n1", "l1", "l2", pairs)
            FormulaFinder.add_node_rel(s, "root", "n1", "l3", pairs)
            FormulaFinder.add_bool_output(s, "root", idx)
            interest = ["root",
                    "n1",
                    "l1", "l1const",
                    "l2", "l2const",
                    "l3", "l3const",
                   ]

        if template == "tictactoe":
            FormulaFinder.add_leaf_cross(s, "l1", FormulaFinder.cells, pairs)
            FormulaFinder.add_leaf_cross(s, "l2", FormulaFinder.cells, pairs)
            FormulaFinder.add_leaf_cross(s, "l3", FormulaFinder.cells, pairs)
            FormulaFinder.add_leaf_cross(s, "l4", FormulaFinder.cells, pairs)
            FormulaFinder.add_node_bool(s, "n1", "l1", "l2", pairs)
            FormulaFinder.add_node_bool(s, "n2", "l3", "l4", pairs)
            FormulaFinder.add_node_bool(s, "root", "n1", "n2", pairs)
            FormulaFinder.add_bool_output(s, "root", idx)
            interest = ["root",
                        "n1", "n2",
                        "l1", "l2", "l3", "l4"
                        ]


        print(s)
        if s.check() == sat:
            model = s.model()
            print("MODEL")
            vals = []
            for v in model:
                vals.append(v)
            vals = sorted(vals, key=str)

            for v in vals:
                print(v, "\t", model[v])

            ret = {}
            for x in interest:
                ret[x] = model[Int(x)]
            return ret

        else:
            return None


# print("\n\n\n\n\nTesting")
# FormulaFinder.template = "tictactoe"
# FormulaFinder.cells = 4
# points = [[0,0,0,0], [0,0,0,1], [1,0,0,0]]
# mins = [0,0,0,0]
# maxs = [1,0,0,1]
# f = FormulaFinder.find_boolean("tictactoe", points, mins, maxs, timeout=5000)
# print("Points: ", points)
# print(f)
# print(FormulaFinder.print_boolean(f, 0))
