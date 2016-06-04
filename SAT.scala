import scala.collection.mutable.Stack
import scala.collection.mutable.MutableList
import swing._
import event._
import BorderPanel.Position._

object Config {
    val DEBUG = true
}

object Printer {
    def info(any: Any*) {
        any.map(string).foreach(print)
        println("")
    }

    def debug(any: Any*) {
        if (Config.DEBUG) {
            info(any:_*)
        }
    }

    def string(any: Any): String = {
        def listToString(list: List[_]): String = list(0) match {
            case _: Conjunction => list.map { c => c.toString }.reduce { (a, b) =>
                a + " + " + b
            }
            
            case _: Element => list.map { e => e.toString }.reduce { (a, b) =>
                a + " " + b
            }

            case _ => list.toString 
        }

        return any match {
            case list: List[_] => listToString(list)
            case list: MutableList[_] => listToString(list.toList)
            case _ => any.toString 
        }
    }
}

trait Element {
    val priority: Int = 0
}

case class Identifier(name: String) extends Element {
    override def toString = name
}

trait Bracket extends Element

case object OpenBracket extends Bracket {
    override def toString = "("
}
case object CloseBracket extends Bracket {
    override def toString = ")"
}

trait Operator extends Element

case object NegationOperator extends Operator {
    override val priority = 3
    override def toString = "!"
}
case object ConjunctionOperator extends Operator {
    override val priority = 2
    override def toString = "."
}
case object DisjunctionOperator extends Operator {
    override val priority = 1
    override def toString = "+"
}

class Variable(_name: String, _value: Boolean) {
    def this(name: String) = this(name, true)

    val value = _value
    val name = _name

    override def toString = if (value) name else "!" + name
}

class Conjunction(_variables: List[Variable]) {
    override def toString: String = variables.map { v => v.toString }.reduce { (a,b) => 
        a + "." + b
    }

    val variables: List[Variable] = _variables
}

class ElementStream(string: String) {
    var position = 0

    def element(token: String): Element = token match {
        case "(" => OpenBracket
        case ")" => CloseBracket
        case "." => ConjunctionOperator
        case "+" => DisjunctionOperator 
        case "!" => NegationOperator
        case _ => Identifier(token)
    }

    def isSymbol(s: String) = element(s) match {
        case Identifier(_) => false
        case _ => true
    }

    def readElement(): Element = {
        def read(s: String): String = {
            if (end) {
                return s
            }

            val c: String = "" + string(position)   
            
            if (isSymbol(c)) { 
                if (s == "") {
                    position += 1
                    return c
                }

                return s
            }

            position += 1
            return read(s + c.trim)
        }

        return element(read(""))
    }

    def end = position >= string.length
}

object PostfixBuilder {
    def build(expression: String): List[Element] = {
        val elementStream = new ElementStream(expression)

        val postfix: MutableList[Element] = MutableList()
        val stack: Stack[Element] = Stack()

        while (!elementStream.end) {
            val element = elementStream.readElement()

            element match {
                case Identifier(_) => 
                    postfix += element

                case OpenBracket => 
                    stack.push(element)

                case CloseBracket => 
                    while (!stack.isEmpty && stack.top != OpenBracket) {
                        postfix += stack.pop()
                    }
                    stack.pop()
                
                case _: Operator =>
                    while (!stack.isEmpty && stack.top.priority >= element.priority) {
                        postfix += stack.pop()
                    }

                    stack.push(element)
            }
            
        }

        while (!stack.isEmpty) {
            postfix += stack.pop()
        }

        return postfix.toList
    }
}

object DNFBuilder {

    def disjunction(conjunctions1: List[Conjunction], conjunctions2: List[Conjunction]): List[Conjunction] = {
        if (conjunctions1.isEmpty) {
            return conjunctions2
        }
        if (conjunctions2.isEmpty) {
            return conjunctions1
        }

        val result = conjunctions1 ++ conjunctions2
       
        Printer.debug("disjunction ", conjunctions1, " || ", conjunctions2, " -> ", result)

        return result
    }
    
    def conjunction(conjunctions1: List[Conjunction], conjunctions2: List[Conjunction]): List[Conjunction] = {
        if (conjunctions1.isEmpty) {
            return conjunctions2
        }
        if (conjunctions2.isEmpty) {
            return conjunctions1
        }

        val result: MutableList[Conjunction] = MutableList()

        for (c1 <- conjunctions1) {
            for (c2 <- conjunctions2) {
                result += new Conjunction(c1.variables ++ c2.variables)
            }
        }

        Printer.debug("conjunction ", conjunctions1, " || ", conjunctions2, " -> ", result)

        return result.toList
    }

    def negateConjunction(conjunction: Conjunction): List[Conjunction] = {
        val result: MutableList[Conjunction] = MutableList()

        for (v <- conjunction.variables) {
            val variable = new Variable(v.name, !v.value)
            result += new Conjunction(List(variable))
        }

        return result.toList
    }

    def negation(conjunctions: List[Conjunction]): List[Conjunction] = {
        var result: List[Conjunction] = List()
        for (conj <- conjunctions) {
            val neg = negateConjunction(conj)
            result = conjunction(result, neg)
        }

        Printer.debug("negation ", conjunctions, " -> ", result)

        return result
    }

    def build(expression: String): List[Conjunction] = {
        val postfix = PostfixBuilder.build(expression)
        Printer.info("Postfix: ", postfix)

        val stack: Stack[List[Conjunction]] = Stack()

        for (element <- postfix) {
            Printer.debug("element ", element)

            element match {
                case NegationOperator =>
                    val op = stack.pop()
                    stack.push(negation(op))

                case ConjunctionOperator =>
                    val op2 = stack.pop()
                    val op1 = stack.pop()
                    stack.push(conjunction(op1, op2))

                case DisjunctionOperator =>
                    val op2 = stack.pop()
                    val op1 = stack.pop()
                    stack.push(disjunction(op1, op2))
                
                case Identifier(name) =>
                    val variable = new Variable(name)
                    stack.push(List(new Conjunction(List(variable))))

                case _ => ;
            }

        }

        return stack.top
    }
}

object SATSolver {

    def evaluate(conjunction: Conjunction): Boolean = {
        def unique(variables: List[Variable]) = variables.groupBy {v => v.name}.map(kv => kv._2.head).toList

        val positive = unique(conjunction.variables.filter { v => v.value })
        val negative = unique(conjunction.variables.filter { v => !v.value })

        val all = unique(positive ++ negative)

        return all.length == positive.length + negative.length
    }

    def solve(expression: String): Boolean =  {
        Printer.info(expression)

        val dnf = DNFBuilder.build(expression)
        Printer.info("DNF: ", dnf)

        def eval(i: Int): Boolean = 
            if (i >= dnf.length) { false } 
            else if (evaluate(dnf(i))) { true } 
            else { eval(i+1) }

        val result = eval(0)

        Printer.info("---")
        Printer.info(result)
        Printer.info("---")

        return result
        
    }
}

object SAT extends SimpleSwingApplication {
  def top = new MainFrame {
        preferredSize = new Dimension(600, 200)
        title = "SAT Solver"

        val inputTextField = new TextArea

        val solveButton = new Button {
          text = "Solve"
        }

        val resultLabel = new Label {
            text = " "
            listenTo(solveButton, inputTextField)
          
            def solve() {
                if (inputTextField.text.length > 0) {
                    text = "<html><font color = red>" + SATSolver.solve(inputTextField.text) + "</font></html>"
                }
            }
          
            reactions += {
                case ButtonClicked(_) | EditDone(_) => solve()
            }
        }

        val centered = new FlowPanel {
            contents.append(new BoxPanel(Orientation.Vertical) {
                contents.append(solveButton, resultLabel)
            })
        }

        contents = new BorderPanel {    
            layout(inputTextField) = Center
            layout(centered) = South
            border = Swing.EmptyBorder(10, 10, 10, 10)
        }
    }
}

SAT.main(null)

//JO
//SATSolver.solve("a . ! b + ! ( ( c . d . ! d ) + u . v ) + ! e . f");

// NE
//SATSolver.solve("aaa.( bbb + ccc ).!bbb.!ccc");

// a) T = {(p ⇒ q) ∧ r, q ∧ r, r ⇒ s, p ∧ ¬s} NE
//SATSolver.solve("((!p+q).r) . (q.r) . (!r.s) . (p.!s)");

// b) F = {(p ∧ q ∧ r) ⇒ [(s ∧ ¬t) ∨ (¬s ∧ t)], q ∧ r, ¬s, ¬t, p} NE
//SATSolver.solve("( !(p + q + r) + (s.!t + !s.t) ) . (q+r) . (!s) . (!t) . (p)");

// c) G = {q ⇒ r, r ⇒ p, q ⇒ p} JO
//SATSolver.solve("(!q + r) . (!r + p) . (!q + p)");

// d) Y = {q ⇒ r, r ⇒ p, ¬(q ⇒ p)} NE
//SATSolver.solve("(!q + r).(!r + p).!(!q + p)");

//e) Z = {(p ∨ q) ⇔ r, r, ¬p, q} JO
//SATSolver.solve("((p+q).r + !(p+q).!r) . (r) . (!p) . (q)");

