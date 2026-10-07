package Argumentation.LAF.Domain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import net.objecthunter.exp4j.Expression;
import net.objecthunter.exp4j.ExpressionBuilder;
import net.objecthunter.exp4j.function.Function;

/**
 * Executes the inferential process over a knowledge program composed of
 * user-defined facts and rules, applying the label algebra (support,
 * aggregation and conflict) defined for each label.
 * <p>
 * This class is the core of the reasoning engine: it builds new facts
 * whenever a rule is activated, propagating labels accordingly.
 * </p>
 *
 * <p>
 * The inference flow executed by {@link #run(Map, List, List)} is:
 * </p>
 * <ol>
 *   <li>Load initial facts</li>
 *   <li>Iteratively activate rules when their body predicates are present</li>
 *   <li>Apply <b>support</b> to combine rule and parent facts</li>
 *   <li>Apply <b>aggregation</b> when multiple facts derive the same new fact</li>
 *   <li>Detect <b>conflict</b> when a fact and its negation appear</li>
 *   <li>Build an {@link ArgumentativeGraph} with all edge relations</li>
 * </ol>
 *
 * <h3>Label Interpretation</h3>
 * <ul>
 *   <li>If attributes parse as doubles -> numeric algebra via exp4j</li>
 *   <li>If not -> interpreted as sets of strings, combined with a symbolic
 *       operator ({@code Union}, {@code Intersection} or {@code Difference}).
 *       Any of the three is valid for support, aggregation and conflict.</li>
 * </ul>
 *
 * <h3>Returned Structure</h3>
 * The engine returns an {@link ArgumentativeGraph} containing:
 * <ul>
 *   <li>A map {@code parent -> list of derived facts}</li>
 *   <li>A list of conflict pairs</li>
 * </ul>
 * 
 * @JaviDebórtoli
 */
public class InferenceEngine {
    /** Stores argumentation edges used when constructing the graph. */
    private final Map<KnowledgePiece, List<Fact>> edges;
    /** Active list of facts during the inference cycle. */
    private final List<Fact> facts;
    /** Rule set composing the program being evaluated. */
    private final List<Rule> rules;
    /** Matrix storing the label algebra functions. */
    private final String[][] functions;
    /** Temporary list of edges that need to be removed after conflict resolution. */
    private final List<KnowledgePiece> removableEdges;
    /** Pairs of contradictory facts detected during the conflict phase. */
    private final List<PairInConflict> conflictiveNodes;

    /**
     * Propagation mode. {@code true} follows Budán et al. (2017), Definition 8(iii) and
     * Algorithm 2: the support of a derived fact is computed from the <b>weakened</b>
     * valuations (δ) of its premises. {@code false} keeps the legacy behaviour of this
     * engine: support uses the accrued valuations (μ) and conflicts are resolved once,
     * after the inference fixpoint. Selected with the system property
     * {@code laf.propagation} or the environment variable {@code LAF_PROPAGATION}
     * ({@code weakened} | {@code accrued}); the default is {@code weakened}.
     */
    private final boolean propagateWeakened;
    /** Original labels F(X) of the facts given in the program, keyed by {@code name(argument)}. */
    private final Map<String, String[]> initialLabels;
    /** Rule applications that derived each fact, keyed by {@code name(argument)} of the conclusion. */
    private final Map<String, List<Derivation>> derivations;

    /** One rule application: the rule, the literal keys of its premises and the per-rule fact it produced. */
    private record Derivation(Rule rule, List<String> premiseKeys, Fact ruleFact) {}

    /** Maximum number of Jacobi iterations when relabeling with weakened premises. */
    private static final int MAX_RELABEL_ITERATIONS = 500;
    /** Convergence tolerance of the relabeling loop. */
    private static final double RELABEL_EPSILON = 1e-12;

    /** Custom exp4j function exposing Math.min(X, Y) as min(X,Y) in user expressions. */
    private static final Function MIN_FUNCTION = new Function("min", 2) {
        @Override
        public double apply(double... args) {
            return Math.min(args[0], args[1]);
        }
    };

    /** Custom exp4j function exposing Math.max(X, Y) as max(X,Y) in user expressions. */
    private static final Function MAX_FUNCTION = new Function("max", 2) {
        @Override
        public double apply(double... args) {
            return Math.max(args[0], args[1]);
        }
    };

    /** Symbolic operator keyword: set union, usable in support, aggregation and conflict. */
    private static final String SYMBOLIC_UNION = "Union";
    /** Symbolic operator keyword: set intersection, usable in support, aggregation and conflict. */
    private static final String SYMBOLIC_INTERSECTION = "Intersection";
    /** Symbolic operator keyword: set difference (X \ Y), usable in support, aggregation and conflict. */
    private static final String SYMBOLIC_DIFFERENCE = "Difference";

    /**
     * Creates a new inference engine from lists of facts, rules,
     * and the label algebra function table.
     * 
     * @param facts      The initial list of known facts. These form the base
     *                   knowledge from which the inference process begins.
     * @param rules      The set of rules that may produce new facts during
     *                   evaluation. These rules are not modified by the engine.
     * @param functions  A 2D array representing the label algebra
     */
    public InferenceEngine(List<Fact> facts, List<Rule> rules, String[][] functions) {
        this(facts, rules, functions, defaultPropagateWeakened());
    }

    /**
     * Creates a new inference engine choosing the propagation mode explicitly.
     *
     * @param propagateWeakened {@code true} to propagate the weakened valuations δ of the
     *                          premises (Budán et al. 2017, Def. 8(iii)); {@code false} for
     *                          the legacy accrued-valuation propagation.
     */
    public InferenceEngine(List<Fact> facts, List<Rule> rules, String[][] functions, boolean propagateWeakened) {
        this.edges = new HashMap<>();
        this.facts = facts;
        this.rules = rules;
        this.functions = functions;
        this.removableEdges = new ArrayList<>();
        this.conflictiveNodes = new ArrayList<>();
        this.propagateWeakened = propagateWeakened;
        this.derivations = new LinkedHashMap<>();
        this.initialLabels = new LinkedHashMap<>();
        for (Fact fact : facts) {
            initialLabels.put(literalKey(fact), fact.getAttributes());
        }
    }

    /** Reads the propagation mode from {@code laf.propagation} / {@code LAF_PROPAGATION}; default weakened. */
    private static boolean defaultPropagateWeakened() {
        String mode = System.getProperty("laf.propagation");
        if (mode == null || mode.isBlank()) {
            mode = System.getenv("LAF_PROPAGATION");
        }
        return mode == null || mode.isBlank() || !mode.trim().equalsIgnoreCase("accrued");
    }

    /** Returns the propagation mode in use. */
    public boolean isPropagateWeakened() {
        return propagateWeakened;
    }

    /**
     * Applies a symbolic (set-based) label operator between two qualitative label
     * values, used as the fallback whenever numeric evaluation of an expression
     * fails because the attributes are sets of strings rather than doubles.
     * <p>
     * Both operands are tokenized by splitting on whitespace before the operator
     * is applied, so that multi-word values (e.g. the result of a previous
     * {@code Union}) are treated as proper sets rather than single opaque tokens.
     * This same helper backs support, aggregation and conflict, so any of
     * {@code Union}, {@code Intersection} or {@code Difference} can be used in
     * any of the three operations.
     * </p>
     *
     * @param operatorName  the symbolic keyword configured for this label
     *                      ({@link #SYMBOLIC_UNION}, {@link #SYMBOLIC_INTERSECTION}
     *                      or {@link #SYMBOLIC_DIFFERENCE})
     * @param leftValue     the left-hand operand (plays the role of {@code X})
     * @param rightValue    the right-hand operand (plays the role of {@code Y})
     * @return              the resulting set, rendered back as a space-joined string
     * @throws IllegalArgumentException if {@code operatorName} is not a recognized
     *                      symbolic operator
     */
    private String applySymbolicOperator(String operatorName, String leftValue, String rightValue) {
        LinkedHashSet<String> left = new LinkedHashSet<>(Arrays.asList(leftValue.split(" ")));
        Set<String> right = new LinkedHashSet<>(Arrays.asList(rightValue.split(" ")));

        switch (operatorName) {
            case SYMBOLIC_UNION -> left.addAll(right);
            case SYMBOLIC_INTERSECTION -> left.retainAll(right);
            case SYMBOLIC_DIFFERENCE -> left.removeAll(right);
            default -> throw new IllegalArgumentException(
                    "Unsupported label operator for qualitative attributes: '" + operatorName + "'");
        }

        return String.join(" ", left);
    }

    /**
     * Executes the complete inference cycle and constructs the argumentative structure.
     * <p>
     * This method drives the full process:
     * <ol>
     *   <li>Iterates through all rules and attempts inference for every argument</li>
     *   <li>Derives new facts when rule activation is successful</li>
     *   <li>Checks for aggregation when duplicate facts appear</li>
     *   <li>Marks edges for removal when a fact must be replaced by its aggregated version</li>
     *   <li>Detects contradictions (p(X) vs ~p(X)) and computes weakened labels</li>
     * </ol>
     *
     * When no new facts are generated and all aggregations/conflicts have been processed,
     * the system is considered stable and returns the internal graph representation.
     *
     * @return an {@link ArgumentativeGraph} that connects parents (Facts/Rules)
     * to derived Facts, plus conflict pairs for visualization.
     */
    public ArgumentativeGraph buildTree() {
        List<Fact> potentialFacts = new ArrayList<>();
        boolean anyNewFact;
        Fact newFact = null;
        int bodyPartsVerified;
        List<String> arguments = new ArrayList<>();
        // All arguments different from the facts are obtained.
        for (Fact fact : facts) {
            if (!arguments.contains(fact.getArgument())) {
                arguments.add(fact.getArgument());
            }
        }
        
        do {
            anyNewFact = false; // Indicates whether the graph has been modified and the cycle must be repeated.

            for (String argument : arguments) { // Arguments cycle
                for (Rule rule : rules) { // Rules cycle

                    potentialFacts.clear();
                    bodyPartsVerified = 0;

                    for (String bodypart : rule.getBody()) { // Body cycle for each rule
                        for (Fact fact : facts) { // Facts cycle                    
                            
                            if ( bodypart.equals(fact.getName()) && fact.getArgument().equals(argument)) {    
                                newFact = new Fact(rule.getHead(), fact.getArgument(), null); // New fact created
                                potentialFacts.add(fact); // The fact is added to the fulfilled predicates of the rule.
                                bodyPartsVerified++;
                            }
                            
                        }
                    }

                    if ( bodyPartsVerified == rule.getBody().size() 
                            && !alreadyExists(newFact, rule) 
                            && !anyAggregation(newFact) ) {

                        addFact(potentialFacts, newFact, rule); // New fact added 
                        anyNewFact = true; // Indicates that the major cycle must be repeated
                    } else if ( bodyPartsVerified == rule.getBody().size() 
                            && !alreadyExists(newFact, rule) 
                            && anyAggregation(newFact) ){

                        doAggregation(potentialFacts, newFact, rule); // New aggregated fact added
                        anyNewFact = true; // Indicates that the major cycle must be repeated
                    }
                }
            }
        } while (anyNewFact);
        
        conflict(); // Conflicts between facts are resolved

        if (propagateWeakened) {
            // Budán et al. (2017), Def. 8(iii) / Algorithm 2: recompute every label so that the
            // support of each conclusion uses the weakened valuations of its premises.
            relabelWithWeakenedPremises();
        }

        return new ArgumentativeGraph(edges, conflictiveNodes);
    }
    
    /**
     * Registers a newly inferred fact into the inference state and updates the graph structure.
     * <p>
     * This method is called when a rule has been successfully activated and a conclusion
     * (new fact) can be generated from a set of premises.
     * </p>
     *
     * <h3>Operational steps performed:</h3>
     * <ol>
     *   <li>Computes the labels of the new fact by applying the SUPPORT operation:
     *       <pre>support(premises, rule)</pre>
     *   </li>
     *   <li>Adds the new fact to the global list of known facts</li>
     *   <li>Creates a SUPPORT edge from the rule to the new fact</li>
     *   <li>Creates AGGREGATION-candidate edges from all premises to the new fact</li>
     * </ol>
     *
     * @param potentialFacts The list of existing facts that matched the rule body
     * and enabled the inference. They become parents in the graph.
     * @param newFact The fact generated as a consequence of firing the rule.
     * @param rule The rule used to derive the new fact; origin point of the SUPPORT edge.
     * 
     * This method does not check for duplicates or conflicts; that is handled afterward
     * by aggregation and conflict-management routines.
     */
    private void addFact (List<Fact> potentialFacts, Fact newFact, Rule rule) {
        // Calculate label values 
        newFact.setAttributes( calculateSupport (potentialFacts, rule) );
        recordDerivation(newFact, rule, potentialFacts, newFact);
        // Add new fact to facts list
        facts.add(newFact);
        // Add edge between the activated rule and the new fact.
        if (!edges.containsKey(rule)) {
            edges.put(rule, new ArrayList<>());
        }
        edges.get(rule).add(newFact);
        // Add edge between the ancestors facts and the new fact.
        for (Fact potentialFact : potentialFacts) {
            if (!edges.containsKey(potentialFact)) {
                edges.put(potentialFact, new ArrayList<>());
            }
            edges.get(potentialFact).add(newFact);
        }
    }
    
    /**
     * Computes the SUPPORT operation for a newly inferred fact according to the
     * label algebra defined in {@code functions[i][0]}.
     * <p>
     * This operation combines the labels of the premises (facts that activated the rule)
     * and the label of the rule itself. The computation mechanism depends on the type of
     * labels of the program:
     *
     * <h3>Numeric evaluation (default attempt)</h3>
     * If the labels can be parsed as {@code double}, the method:
     * <ul>
     *   <li>Evaluates the expression in {@code functions[i][0]} using exp4j</li>
     *   <li>Sequentially combines: accumulator -> premises -> rule</li>
     *   <li>Clamps the numeric result to the range {@code [0.0, 1.0]}</li>
     * </ul>
     *
     * <h3>Symbolic / Set-based fallback</h3>
     * If numeric evaluation fails (NumberFormatException), the method performs
     * a symbolic operation via {@link #applySymbolicOperator(String, String, String)},
     * folding premises then the rule's own value in order. Any of {@code Union},
     * {@code Intersection} or {@code Difference} may be configured.
     *
     * @param potentialFacts    The list of facts that satisfied the body of the rule
     *                          and enable the derivation of a new fact.
     * @param rule              The rule being activated; its label participates last in the
     *                          calculation and completes the support propagation.
     * 
     * @return  A {@code String[]} vector of labels representing the result of applying
     *          the SUPPORT algebra to the given premises and rule.
     */
    private String[] calculateSupport (List<Fact> potentialFacts, Rule rule) {
        String[] atributtes = new String[ potentialFacts.getFirst().getAttributes().length ];
        Expression expression;

        for (int i = 0; i < atributtes.length ; i++) {
            // Reemplazar los valores de X y Y, y evaluar la funcion para cada uno de los antecedentes
            try {
                // El fold arranca en el valor real de la primera premisa (no en "0.0" artificial),
                // para no imponer un elemento neutro incorrecto a operadores como min(X,Y).
                Iterator<Fact> premises = potentialFacts.iterator();
                atributtes[i] = premises.next().getAttributes()[i];

                while (premises.hasNext()) {
                    Fact fact = premises.next();
                    // Parsear X e Y ANTES de construir la expresion: si los atributos son
                    // cualitativos (ej. "red"), esto debe fallar aca con NumberFormatException,
                    // sin intentar compilar el operador simbolico (ej. "Union") como expresion numerica.
                    double xValue = Double.parseDouble(atributtes[i]);
                    double yValue = Double.parseDouble(fact.getAttributes()[i]);
                    expression = new ExpressionBuilder( functions[i][0] )
                        .variables("X", "Y")
                        .functions(MIN_FUNCTION, MAX_FUNCTION)
                        .build()
                        .setVariable("X", xValue)
                        .setVariable("Y", yValue);

                    atributtes[i] = String.valueOf(expression.evaluate());
                }
                // Reemplazar los valores de X y Y, y evaluar la funcion para la regla
                double xValue = Double.parseDouble(atributtes[i]);
                double yValue = Double.parseDouble(rule.getAttributes()[i]);
                expression = new ExpressionBuilder( functions[i][0] )
                        .variables("X", "Y")
                        .functions(MIN_FUNCTION, MAX_FUNCTION)
                        .build()
                        .setVariable("X", xValue)
                        .setVariable("Y", yValue);

                atributtes[i] = String.valueOf(expression.evaluate());
                // Ubicar los valores en el intervalo [0, 1]
                if (Double.parseDouble(atributtes[i])>1) {
                    atributtes[i] = "1.0";
                } else if (Double.parseDouble(atributtes[i])<0) {
                    atributtes[i] = "0.0";
                }
            } catch (NumberFormatException exception1) {
                // Atributos cualitativos: se rearma el fold usando el operador simbolico
                // configurado (Union, Intersection o Difference), en el mismo orden que
                // el fold numerico (premisas en orden, luego el atributo de la regla).
                Iterator<Fact> premises = potentialFacts.iterator();
                String accumulated = premises.next().getAttributes()[i];

                while (premises.hasNext()) {
                    accumulated = applySymbolicOperator(functions[i][0], accumulated, premises.next().getAttributes()[i]);
                }

                atributtes[i] = applySymbolicOperator(functions[i][0], accumulated, rule.getAttributes()[i]);
            }
        }

        return atributtes;
    }
    
    /**
     * Determines whether two facts represent the same logical statement in the
     * knowledge base, ignoring their attribute values.
     * <p>
     * Two facts are considered equal if and only if:
     * <ul>
     *   <li>They share the same predicate name</li>
     *   <li>They refer to the same argument</li>
     * </ul>
     *
     * Attribute vectors (original or delta) are <b>not</b> compared here. This is
     * intentional: equality is defined at the logical level (predicate + argument),
     * while label differences are handled later during aggregation or conflict.
     *
     * @param firstFact  The first fact to compare
     * @param secondFact The second fact to compare
     * @return {@code true} if both facts describe the same logical statement,
     *         {@code false} otherwise
     */
    private boolean equalFacts (Fact firstFact, Fact secondFact) {
        return firstFact.getName().equals(secondFact.getName()) 
                && firstFact.getArgument().equals(secondFact.getArgument());
    } 
    
    /**
     * Checks whether a fact that would be derived by a given rule
     * has already been produced by that same rule in the past.
     *
     * <p>
     * This method does <b>not</b> check global fact duplication. Instead, it verifies
     * a more specific condition:
     * <br><br>
     * <b>"Has this rule previously generated a fact with the same
     * predicate and argument?"</b>
     * </p>
     *
     * <h3>Equality Criterion</h3>
     * The comparison is logical (semantic), not syntactic:
     * <ul>
     *   <li>Same predicate name</li>
     *   <li>Same argument</li>
     * </ul>
     * Labels are ignored; if label differences arise, the aggregation procedure
     * will handle them later.
     *
     * @param newFact The fact that may potentially be derived again
     * @param rule    The rule that would originate the derivation
     * @return {@code true} if the rule has already produced a logically identical fact, {@code false} otherwise.
     */
    private boolean alreadyExists (Fact newFact, Rule rule) {
        boolean existsRule = false;

        for ( Map.Entry<KnowledgePiece, List<Fact>> edge : edges.entrySet() ) {
            for (Fact fact : edge.getValue()) {
                if ( equalFacts(fact, newFact) && edge.getKey() == rule ) {
                    existsRule = true;
                }
            }
        }
        
        return existsRule;
    }
    
    /**
     * Determines whether a newly inferred fact requires aggregation with an
     * existing one already present in the argumentative graph.
     *
     * <p>
     * A fact needs aggregation when there is already another fact that:
     * <ul>
     *   <li>Has the same predicate (name)</li>
     *   <li>Refers to the same argument</li>
     * </ul>
     * regardless of their attribute values.
     * </p>
     *
     * <p>
     * The search is performed through the current graph structure stored in
     * {@code edges}. A match triggers the aggregation process which will merge
     * labels, update edges, and unify the fact representation.
     * </p>
     * 
     * @param newFact The newly generated fact whose presence in the graph must be checked
     * @return  {@code true} if a fact with the same name and argument already exists
     *           in the graph, indicating that an aggregation step is required;
     *           {@code false} otherwise
     */
    private boolean anyAggregation(Fact newFact) {
        boolean aggregation = false;

        for (Map.Entry<KnowledgePiece, List<Fact>> entry : edges.entrySet()) {
            KnowledgePiece key = entry.getKey();

            if (key instanceof Fact && equalFacts((Fact) key, newFact)) {
                aggregation = true;
                break;
            }

            for (Fact fact : entry.getValue()) {
                if (equalFacts(fact, newFact)) {
                    aggregation = true;
                    break;
                }
            }

            if (aggregation) {
                break;
            }
        }

        return aggregation;
    }

    /**
     * Performs aggregation when a newly inferred fact is logically identical to an
     * existing one (same predicate and argument), preventing duplication in the graph.
     *
     * <p>
     * Aggregation is triggered when {@code anyAggregation(newFact)} is true.
     * Instead of creating a second node for the same fact, the system:
     * </p>
     *
     * <ol>
     *   <li>Locates the existing matching fact (same name + argument)</li>
     *   <li>Removes the outdated version from the knowledge base</li>
     *   <li>Recomputes the new fact's attributes via SUPPORT</li>
     *   <li>Creates edges from the rule and its premises to the new fact</li>
     *   <li>Merges labels with the previous version using {@code calculateAggregation(...)}</li>
     *   <li>Inserts the aggregated fact as the unified representation</li>
     *   <li>Triggers a reorganization of the graph to preserve coherence</li>
     * </ol>
     *
     * <h3>Aggregation rationale</h3>
     * If two derivations lead to the same fact:
     * <pre>
     *    factA(X). {red}        from Rule R1
     *    factA(X). {blue}       from Rule R2
     *
     * -> aggregation ->  factA(X). {red blue}
     * </pre>
     *
     * <h3>Label algebra behavior</h3>
     * <ul>
     *   <li>Numeric: applies the operator defined in {@code functions[i][1]}</li>
     *   <li>Symbolic: falls back to the configured set operator (Union, Intersection or Difference)</li>
     * </ul>
     *
     * <h3>Graph effects</h3>
     * <ul>
     *   <li>Removes the outdated fact instance</li>
     *   <li>Adds new edges from premises and rule to the unified fact</li>
     *   <li>Rebuilds dependency paths to avoid dangling references</li>
     * </ul>
     *
     * @param potentialFacts The list of existing facts that activated the rule
     * @param newFact        The newly derived fact that caused the aggregation trigger
     * @param rule           The rule responsible for producing {@code newFact}
     */
    private void doAggregation(List<Fact> potentialFacts, Fact newFact, Rule rule) {
        Fact auxFact = null;

        for (Fact fact : facts) {
            if (equalFacts(fact, newFact)) {
                auxFact = fact; // The same fact is found
                break;
            }
        }

        if (auxFact != null) {
            facts.remove(auxFact); // The same fact is removed
        } else {
            auxFact = combineFacts(newFact);
        }

        newFact.setAttributes(calculateSupport(potentialFacts, rule)); // Calculate the attributes values
        recordDerivation(newFact, rule, potentialFacts, newFact);
        // Add the edge from the activated rule to the new fact
        if (!edges.containsKey(rule)) {
            edges.put(rule, new ArrayList<>());
        }
        edges.get(rule).add(newFact);
        // Add edges between ancestors and the new fact
        for (Fact potentialFact : potentialFacts) {
            if (!edges.containsKey(potentialFact)) {
                edges.put(potentialFact, new ArrayList<>());
            }
            edges.get(potentialFact).add(newFact);
        }
        // Calculate the attributes values
        Fact aggregatedFact = new Fact(newFact.getName(), newFact.getArgument(), calculateAggregation(newFact, auxFact));
        // Add new fact to facts list
        facts.add(aggregatedFact);
        // Re-build argumentative graph with the new aggregation
        reBuilTree(aggregatedFact);
    }
    
    /**
     * Builds a new unified fact by aggregating all existing occurrences of a fact
     * with the same predicate and argument as {@code newFact}.
     *
     * <p>
     * This method is used as a fallback when an aggregation is required but the
     * matching fact is not found directly in the main fact list (e.g., because it
     * only appears as part of graph edges). Rather than assuming no duplicates
     * exist, the engine performs a search across the graph to collect all fact
     * instances related to the same logical statement.
     * </p>
     *
     * <h3>Operational steps</h3>
     * <ol>
     *   <li>Searches keys and values of {@code edges} (graph structure)</li>
     *   <li>Identifies every fact that matches:
     *      <pre>same predicate AND same argument</pre>
     *   </li>
     *   <li>Accumulates these duplicates in {@code aggregatedFacts}</li>
     *   <li>Delegates label aggregation to {@code calculateAggregation(...)}</li>
     *   <li>Creates and returns a new fact containing the unified label result</li>
     * </ol>
     * 
     * <h3>Label semantics</h3>
     * Numeric labels -> aggregated numerically according to {@code functions[i][1]}
     * Text labels -> combined via the configured set operator (Union, Intersection or Difference)
     *
     * @param newFact   The fact that triggered the aggregation process; its predicate
     *                  and argument determine the search target for combination.
     * @return          A new {@link Fact} instance with merged labels representing the
     *                  unified version of all matching facts found in the graph.
     */
    private Fact combineFacts (Fact newFact) {
        List<Fact> aggregatedFacts = new ArrayList<>();
        // Looking for matching facts in the graph  
        for (Map.Entry<KnowledgePiece, List<Fact>> edge : edges.entrySet()) { 
            if (edge.getKey() instanceof Fact && equalFacts( (Fact) edge.getKey(), newFact) ) {
                aggregatedFacts.add((Fact) edge.getKey());
            }
            
            for (Fact piece : edge.getValue()) {
                if ( equalFacts(piece, newFact) ) {
                    aggregatedFacts.add( piece );
                }
            }
        }
        // The matching facts are combined
        return new Fact(newFact.getName(), newFact.getArgument(), calculateAggregation(aggregatedFacts) );
    }
        
    /**
     * Rebuilds the argumentative graph after an aggregation occurs, ensuring that
     * outdated references to previous fact versions are removed and replaced by
     * correct edges pointing to the newly aggregated fact.
     *
     * <p>
     * This method is invoked after aggregation has produced a unified fact. Its role
     * is to refactor the graph to reflect the updated structure:
     * </p>
     *
     * <h3>Reorganization steps</h3>
     * <ol>
     *   <li>Clears the temporary list of removable edges</li>
     *   <li>Searches the graph for references to old versions of the fact</li>
     *   <li>Marks outdated parents (old fact instances) for removal</li>
     *   <li>Detaches edges that still point to outdated aggregated nodes</li>
     *   <li>Registers the valid parents that must now point toward the new fact</li>
     *   <li>Removes outdated entries from the edge map</li>
     *   <li>Adds fresh edges so dependencies now reference {@code newFact}</li>
     * </ol>
     * 
     * <h3>Graph effects</h3>
     * <ul>
     *   <li>Old nodes representing the same fact cease to function as parents</li>
     *   <li>The graph no longer contains split origins for one fact</li>
     *   <li>Edge cycles caused by older duplicates are eliminated</li>
     * </ul>
     * 
     * @param newFact   The aggregated fact that must become the canonical version of
     *                  the fact in the graph. All references will be redirected to it.
     */
    private void reBuilTree (Fact newFact) {
        removableEdges.clear(); // Cleam removable edges list
        Set<KnowledgePiece> newEdges = new HashSet<>(); // Source facts of the new edges towards the aggregate fact
        // Looking for matching facts in the graph
        for (Map.Entry<KnowledgePiece, List<Fact>> entry : edges.entrySet()) {
            // We are looking for edges that originate in the aggregated nodes.
            if ( entry.getKey() instanceof Fact && equalFacts( (Fact) entry.getKey(), newFact ) ) {
                newEdges.add(entry.getKey());
                removableEdges.add( (Fact) entry.getKey() );
                // Remove the upper nodes from the new aggregation
                eraseUpperNodes( entry.getValue() );
            } else {
                for (Fact fact : entry.getValue()) {
                    if ( equalFacts(fact, newFact) ) {
                        newEdges.add(fact);
                    }
                }
            }
        }
        // Remove edges
        for (KnowledgePiece removableEdge : removableEdges) {
            edges.remove(removableEdge);
        }
        // Add new aggregation edges
        for (KnowledgePiece edge : newEdges) {
            if (!edges.containsKey(edge)) {
                edges.put(edge, new ArrayList<>());
            }
            edges.get(edge).add(newFact);
        }
    }
    
    /**
     * Recursively marks nodes and their parent dependencies for removal when an
     * aggregated fact replaces previous instances in the graph.
     *
     * <p>
     * This method is invoked during the reorganization process triggered by
     * {@code reBuilTree(...)}. Its purpose is to ensure that outdated parent nodes
     * (facts that represented older versions of the same knowledge) are removed
     * from the argumentative graph structure.
     * </p>
     * 
     * <h3>Operational behavior</h3>
     * For each fact in {@code values}:
     * <ol>
     *   <li>If the fact appears as a key in the graph, its children are recursively
     *       processed to propagate removal upward through the derivation chain.</li>
     *   <li>The fact itself is marked for deletion in {@code removableEdges}.</li>
     *   <li>All parents that link to this fact (i.e. those for whom it appears as
     *       a destination in an edge) are also marked for removal.</li>
     * </ol>
     *
     * <h3>Conceptual purpose</h3>
     * When aggregation consolidates multiple fact instances into one canonical fact,
     * this method ensures that:
     * <ul>
     *   <li>Outdated derivation paths are cleaned</li>
     *   <li>No dangling references remain in the graph</li>
     *   <li>Invalid parent nodes are detached before reconstruction</li>
     * </ul>
     * 
     * @param values    The list of outdated fact nodes that must be recursively traced
     *                  and scheduled for removal from the graph structure.
     */
    public void eraseUpperNodes (List<Fact> values) {        
        for (Fact value : values) {
            // Remove upper nodes recursively
            if (edges.containsKey(value)) {
                eraseUpperNodes(edges.get(value));
            }
            // Remove node
            removableEdges.add(value); 
            // Remove edges that have the removed node as their destination
            for (Map.Entry<KnowledgePiece, List<Fact>> entry : edges.entrySet()) {
                for (Fact fact : entry.getValue()) {
                    if ( fact == value ) {
                        removableEdges.add(entry.getKey()); 
                    }
                }
            }
        } 
    }
    
    /**
     * Aggregates the label vectors of two logically equivalent facts to produce
     * a unified attribute representation.
     *
     * <p>
     * This method is used when an aggregation event occurs due to the derivation
     * of a new fact that matches a pre-existing fact (same predicate and argument).
     * Instead of keeping both versions, the system merges their labels using the
     * aggregation operator defined in the program's algebra.
     * </p>
     * 
     * <h3>Numeric mode (primary attempt)</h3>
     * If both labels can be parsed as numeric values:
     * <ul>
     *   <li>The operator {@code functions[i][1]} is interpreted by exp4j</li>
     *   <li>X -> label of {@code newFact}</li>
     *   <li>Y -> label of {@code removableFact}</li>
     *   <li>The result is clamped to the interval [0.0, 1.0]</li>
     * </ul>
     * 
     * <h3>Symbolic mode (fallback)</h3>
     * If numeric parsing fails at any index, the method delegates to
     * {@link #applySymbolicOperator(String, String, String)}. Any of
     * {@code Union}, {@code Intersection} or {@code Difference} may be configured.
     *
     * <h3>Operator reference</h3>
     * The algebra index for aggregation is:
     * <pre>
     * functions[i][1]
     * </pre>
     * where {@code i} matches the label dimension.
     *
     * @param newFact       The newly inferred fact whose labels need to be merged.
     * @param removableFact The pre-existing fact with equivalent predicate and argument.
     * @return              A {@code String[]} representing the aggregated label vector, combining
     *                      both numeric values (clamped to [0,1]) or symbolic sets.
     */
    private String[] calculateAggregation(Fact newFact, Fact removableFact) {
        String[] atributtes = new String[ newFact.getAttributes().length ];
        Expression expression;

        for (int i = 0; i < atributtes.length ; i++) {
            try {
                atributtes[i] = "0.0";
                // Parsear X e Y ANTES de construir la expresion (ver nota en calculateSupport).
                double xValue = Double.parseDouble(newFact.getAttributes()[i]);
                double yValue = Double.parseDouble(removableFact.getAttributes()[i]);
                // Replace X and Y in the expresion
                expression = new ExpressionBuilder( functions[i][1] )
                        .variables("X", "Y")
                        .functions(MIN_FUNCTION, MAX_FUNCTION)
                        .build()
                        .setVariable("X", xValue)
                        .setVariable("Y", yValue);
                // Evaluate the expression with the current parameters
                atributtes[i] = String.valueOf(expression.evaluate());
                // Normalize values
                if (Double.parseDouble(atributtes[i])>1) {
                    atributtes[i] = "1.0";
                } else if (Double.parseDouble(atributtes[i])<0) {
                    atributtes[i] = "0.0";
                }
            } catch (NumberFormatException exception1) {
                atributtes[i] = applySymbolicOperator(functions[i][1], newFact.getAttributes()[i], removableFact.getAttributes()[i]);
            }
        }

        return atributtes;
    }

    /**
     * Aggregates the label vectors of multiple logically equivalent facts in order
     * to produce a single unified attribute representation.
     *
     * <p>
     * This method is typically used when several facts with the same predicate
     * and argument (duplicates) have been discovered in the graph and need to be
     * unified into one canonical fact instance. The aggregation algebra combines
     * all matching labels dimension by dimension.
     * </p>
     * 
     * <h3>Numeric mode (primary attempt)</h3>
     * If every value in the current label index can be parsed as a number:
     * <ul>
     *   <li>The aggregation operator at {@code functions[i][1]} is applied iteratively</li>
     *   <li>First fact initializes the accumulator</li>
     *   <li>Each subsequent fact updates it using exp4j</li>
     *   <li>The result is clamped to {@code [0.0, 1.0]}</li>
     * </ul>
     * 
     * <h3>Symbolic / Set-based fallback</h3>
     * If numeric parsing fails for a dimension, the dimension falls back to
     * {@link #applySymbolicOperator(String, String, String)}, folding all facts
     * in order. Any of {@code Union}, {@code Intersection} or {@code Difference}
     * may be configured; duplicates are removed via {@link LinkedHashSet}.
     *
     * <h3>Algebra reference</h3>
     * Aggregation operator for label index {@code i}:
     * <pre>
     * functions[i][1]
     * </pre>
     * 
     * @param aggregatedFacts   The list of facts that share the same predicate and
     *                          argument, whose label values must be unified.
     * @return                  A {@code String[]} label vector representing the fully merged
     *                          attributes, either numerically aggregated or symbolically unioned.
     */
    private String[] calculateAggregation(List<Fact> aggregatedFacts) {
        String[] atributtes = new String[ aggregatedFacts.getFirst().getAttributes().length ];
        Expression expression;

        for (int i = 0; i < atributtes.length ; i++) {
            try {
                atributtes[i] = null;
            
                for (Fact fact : aggregatedFacts) {
                    if(atributtes[i] == null){
                        atributtes[i] = fact.getAttributes()[i];
                    } else {
                        // Parsear X e Y ANTES de construir la expresion (ver nota en calculateSupport).
                        double xValue = Double.parseDouble(atributtes[i]);
                        double yValue = Double.parseDouble(fact.getAttributes()[i]);
                        // Replace X and Y in the expresion
                        expression = new ExpressionBuilder(functions[i][1])
                                .variables("X", "Y")
                                .functions(MIN_FUNCTION, MAX_FUNCTION)
                                .build()
                                .setVariable("X", xValue)
                                .setVariable("Y", yValue);
                        // Evaluate the expression with the current parameters
                        atributtes[i] = String.valueOf(expression.evaluate());
                    }
                }
                // Normalize values
                if (Double.parseDouble(atributtes[i])>1) {
                    atributtes[i] = "1.0";
                } else if (Double.parseDouble(atributtes[i])<0) {
                    atributtes[i] = "0.0";
                }
            } catch (NumberFormatException exception1) {
                Iterator<Fact> remainingFacts = aggregatedFacts.iterator();
                String accumulated = remainingFacts.next().getAttributes()[i];

                while (remainingFacts.hasNext()) {
                    accumulated = applySymbolicOperator(functions[i][1], accumulated, remainingFacts.next().getAttributes()[i]);
                }

                atributtes[i] = accumulated;
            }
        }

        return atributtes;
    }
    
    /**
     * Detects and processes logical conflicts between facts representing opposite
     * statements (i.e., affirmation vs. explicit negation) and applies the conflict
     * operator defined in the label algebra to weaken their attributes.
     *
     * <p>
     * A conflict is triggered when both of the following conditions hold:
     * <ul>
     *   <li>One fact has a predicate of the form {@code ~p}</li>
     *   <li>Another fact exists with predicate {@code p}</li>
     *   <li>Both facts share the same argument</li>
     * </ul>
     * 
     * <h3>Operational steps</h3>
     * <ol>
     *   <li>Collect all negated facts (predicates containing "~")</li>
     *   <li>For each negated fact, search for its positive counterpart</li>
     *   <li>Apply conflict algebra twice:
     *      <ul>
     *        <li>{@code nf = conflict(nf, pos)}</li>
     *        <li>{@code pos = conflict(pos, nf)}</li>
     *      </ul>
     *   </li>
     *   <li>Update {@code deltaAttributes} for both involved facts</li>
     *   <li>Register the conflict pair in {@code conflictiveNodes}
     *       so an attack edge can be built later</li>
     * </ol>
     * 
     * <h3>Label semantics</h3>
     * The operator used for conflict is: 
     * <pre>
     * functions[i][2]
     * </pre>
     *
     * Two evaluation modes exist:
     * <ul>
     *   <li><b>Numeric:</b> evaluate algebra via exp4j</li>
     *   <li><b>Symbolic:</b> fallback to the configured set operator (Union, Intersection or Difference)</li>
     * </ul>
     * 
     * @implNote
     * This method mutates the state of the engine by modifying the
     * {@code deltaAttributes} of conflicting facts. The original values remain in
     * {@code attributes}, allowing comparison between original and weakened labels.
     *
     * @see #calculateAttack(Fact, Fact)
     */
    private void conflict() {
        List<Fact> negativeFacts = new ArrayList<>();
        String[] Attributte1;
        String[] Attributte2;
        // Capture all denied facts
        for (Fact fact : facts) {
            if (fact.getName().contains("~")) {
                negativeFacts.add(fact);
            }
        }
        
        for (Fact nf : negativeFacts) {
            for (Fact fact : facts) { // Find contradictions
                if (nf.getName().replace("~", "").equals(fact.getName()) &&
                    nf.getArgument().equals(fact.getArgument())) {
                    
                    Attributte1 = calculateAttack(nf, fact);
                    Attributte2 = calculateAttack(fact, nf);
                    
                    nf.setDeltaAttributes(Attributte1);
                    fact.setDeltaAttributes(Attributte2);
                    
                    conflictiveNodes.add(new PairInConflict(nf, fact)); // Calculate delta attributes
                }
            }
        }
    }
    
    /**
     * Applies the conflict (attack) operator to two contradictory facts in order to
     * weaken their label vectors according to the program's conflict algebra.
     *
     * <p>
     * This method is invoked when a pair of facts representing opposite statements
     * (e.g., {@code p(X)} vs {@code ~p(X)}) has been detected. The conflict operator
     * defined at {@code functions[i][2]} is then applied dimension by dimension.
     * </p>
     *
     * <h3>Numeric attack (primary mode)</h3>
     * If both label values can be parsed as numbers:
     * <ul>
     *   <li>The operator in {@code functions[i][2]} is evaluated using exp4j</li>
     *   <li>{@code X ←} value from {@code f1}</li>
     *   <li>{@code Y ←} value from {@code f2}</li>
     *   <li>The result is clamped to the interval {@code [0.0, 1.0]}</li>
     * </ul>
     * 
     * <h3>Symbolic attack (fallback)</h3>
     * If numeric parsing fails, the dimension is processed by
     * {@link #applySymbolicOperator(String, String, String)} with {@code f1} as
     * {@code X} and {@code f2} as {@code Y}. Any of {@code Union},
     * {@code Intersection} or {@code Difference} may be configured; duplicates
     * are removed and insertion order is preserved.
     *
     * <h3>Algebra index reference</h3>
     * The conflict operator is selected via:
     * <pre>
     * functions[i][2]
     * </pre>
     * 
     * @param f1    The first fact involved in the contradiction.
     * @param f2    The opposing fact (negated counterpart or symmetrical target).
     * @return      A {@code String[]} label vector representing the weakened form of
     *              {@code f1} after conflict resolution with {@code f2}.
     */
    private String[] calculateAttack (Fact f1, Fact f2) {
        String[] attributtes = new String[f1.getAttributes().length];
        Expression expression;

        for (int i = 0; i < attributtes.length; i++) {
            try {
                // Parsear X e Y ANTES de construir la expresion (ver nota en calculateSupport).
                double xValue = Double.parseDouble(f1.getAttributes()[i]);
                double yValue = Double.parseDouble(f2.getAttributes()[i]);
                // Replace X and Y in the expresion
                expression = new ExpressionBuilder( functions[i][2] )
                        .variables("X", "Y")
                        .functions(MIN_FUNCTION, MAX_FUNCTION)
                        .build()
                        .setVariable("X", xValue)
                        .setVariable("Y", yValue);

                // Evaluate the expression with the current parameters
                attributtes[i] = String.valueOf(expression.evaluate());
                // Normalize values
                if (Double.parseDouble(attributtes[i])>1) {
                    attributtes[i] = "1.0";
                } else if (Double.parseDouble(attributtes[i])<0) {
                    attributtes[i] = "0.0";
                }
            } catch (NumberFormatException exception1) {
                attributtes[i] = applySymbolicOperator(functions[i][2], f1.getAttributes()[i], f2.getAttributes()[i]);
            }
        }

        return attributtes;
    }

    // ------------------------------------------------------------------------------------
    // Propagation with weakened premises (Budán et al. 2017, Definition 8(iii), Algorithm 2)
    // ------------------------------------------------------------------------------------

    /** Literal key {@code name(argument)} used to identify a fact regardless of its object identity. */
    private static String literalKey(Fact fact) {
        return fact.getName() + "(" + fact.getArgument() + ")";
    }

    /** Key of the contradictory literal: {@code p(a)} for {@code ~p(a)} and vice versa. */
    private static String oppositeKey(Fact fact) {
        String name = fact.getName();
        String opposite = name.startsWith("~") ? name.substring(1) : "~" + name;
        return opposite + "(" + fact.getArgument() + ")";
    }

    /**
     * Records that {@code conclusion} was derived by applying {@code rule} to {@code premises}.
     * Premises are stored by literal key, because the engine may later replace a premise object
     * by its aggregated version and re-derive the conclusion; a repeated application of the same
     * rule over the same premises replaces the previous record instead of duplicating it.
     */
    private void recordDerivation(Fact conclusion, Rule rule, List<Fact> premises, Fact ruleFact) {
        List<String> keys = new ArrayList<>();
        for (Fact premise : premises) {
            keys.add(literalKey(premise));
        }
        List<Derivation> list = derivations.computeIfAbsent(literalKey(conclusion), k -> new ArrayList<>());
        list.removeIf(d -> d.rule() == rule && d.premiseKeys().equals(keys));
        list.add(new Derivation(rule, keys, ruleFact));
    }

    /** Evaluates one binary numeric operator of the algebra and clamps the result to [0, 1]. */
    private double evaluate(String operator, double x, double y) {
        double value = new ExpressionBuilder(operator)
                .variables("X", "Y")
                .functions(MIN_FUNCTION, MAX_FUNCTION)
                .build()
                .setVariable("X", x)
                .setVariable("Y", y)
                .evaluate();
        if (value > 1) {
            return 1.0;
        }
        if (value < 0) {
            return 0.0;
        }
        return value;
    }

    private static double[] parseLabels(String[] labels) {
        double[] values = new double[labels.length];
        for (int i = 0; i < labels.length; i++) {
            values[i] = Double.parseDouble(labels[i]);
        }
        return values;
    }

    private static String[] formatLabels(double[] values) {
        String[] labels = new String[values.length];
        for (int i = 0; i < values.length; i++) {
            labels[i] = String.valueOf(values[i]);
        }
        return labels;
    }

    /**
     * Support of one rule application, folded exactly like {@link #calculateSupport}: the first
     * premise, then each following premise, then the rule label; but using the <b>weakened</b>
     * valuations δ of the premises. Returns {@code null} when a premise is not (yet) labeled.
     */
    private double[] supportFromWeakened(Derivation derivation, Map<String, double[]> delta, int labelCount) {
        double[] support = new double[labelCount];
        double[] ruleLabels = parseLabels(derivation.rule().getAttributes());
        for (int i = 0; i < labelCount; i++) {
            Double accumulated = null;
            for (String premiseKey : derivation.premiseKeys()) {
                double[] premise = delta.get(premiseKey);
                if (premise == null) {
                    return null;
                }
                accumulated = accumulated == null ? premise[i] : evaluate(functions[i][0], accumulated, premise[i]);
            }
            if (accumulated == null) {
                return null;
            }
            support[i] = evaluate(functions[i][0], accumulated, ruleLabels[i]);
        }
        return support;
    }

    /**
     * Recomputes μ and δ of every fact so that they satisfy the labeling equations of
     * Budán et al. (2017), Definition 8:
     * <ul>
     *   <li>μ(X) = F(X) ⊕ ⊕<sub>s</sub>( ⊙<sub>t</sub> δ(premise<sub>t</sub>) ⊙ rule<sub>s</sub> ) for a fact of the
     *       program that is also derived; without F(X) for a purely derived fact;
     *       μ(X) = F(X) for a fact without derivations.</li>
     *   <li>δ(X) = μ(X) ⊖ μ(∼X) when ∼X exists, otherwise δ(X) = μ(X).</li>
     * </ul>
     * The equations are solved by Jacobi iteration starting from the legacy values. For an
     * acyclic argumentation graph (no blocking conflict cycles) the iteration reaches the
     * exact solution after at most depth+1 sweeps; with conflict cycles it approximates a
     * fixed point of the system (the article leaves that case to an external solver).
     * Qualitative (symbolic) labels are not relabeled: the legacy values are kept.
     */
    private void relabelWithWeakenedPremises() {
        Map<String, Fact> canonical = new LinkedHashMap<>();
        for (Fact fact : facts) {
            canonical.put(literalKey(fact), fact);
        }
        if (canonical.isEmpty()) {
            return;
        }
        Map<String, double[]> mu = new LinkedHashMap<>();
        Map<String, double[]> delta = new LinkedHashMap<>();
        Map<String, double[]> base = new LinkedHashMap<>();
        int labelCount;
        try {
            labelCount = canonical.values().iterator().next().getAttributes().length;
            for (Map.Entry<String, Fact> entry : canonical.entrySet()) {
                mu.put(entry.getKey(), parseLabels(entry.getValue().getAttributes()));
                delta.put(entry.getKey(), parseLabels(entry.getValue().getDeltaAttributes()));
            }
            for (Map.Entry<String, String[]> entry : initialLabels.entrySet()) {
                base.put(entry.getKey(), parseLabels(entry.getValue()));
            }
            for (Rule rule : rules) {
                parseLabels(rule.getAttributes());
            }
        } catch (NumberFormatException symbolicLabels) {
            return; // qualitative algebra: keep the legacy labels
        }

        for (int iteration = 0; iteration < MAX_RELABEL_ITERATIONS; iteration++) {
            double maxChange = 0.0;
            Map<String, double[]> nextMu = new LinkedHashMap<>();
            for (String key : canonical.keySet()) {
                double[] current = mu.get(key);
                double[] next = new double[labelCount];
                double[] initial = base.get(key);
                List<Derivation> applications = derivations.getOrDefault(key, List.of());
                for (int i = 0; i < labelCount; i++) {
                    Double accumulated = initial == null ? null : initial[i];
                    for (Derivation derivation : applications) {
                        double[] support = supportFromWeakened(derivation, delta, labelCount);
                        if (support == null) {
                            continue;
                        }
                        accumulated = accumulated == null
                                ? support[i]
                                : evaluate(functions[i][1], support[i], accumulated);
                    }
                    next[i] = accumulated == null ? current[i] : accumulated;
                    maxChange = Math.max(maxChange, Math.abs(next[i] - current[i]));
                }
                nextMu.put(key, next);
            }
            Map<String, double[]> nextDelta = new LinkedHashMap<>();
            for (Map.Entry<String, Fact> entry : canonical.entrySet()) {
                String key = entry.getKey();
                String opposite = oppositeKey(entry.getValue());
                double[] own = nextMu.get(key);
                double[] other = nextMu.get(opposite);
                double[] next = new double[labelCount];
                for (int i = 0; i < labelCount; i++) {
                    next[i] = other == null ? own[i] : evaluate(functions[i][2], own[i], other[i]);
                    maxChange = Math.max(maxChange, Math.abs(next[i] - delta.get(key)[i]));
                }
                nextDelta.put(key, next);
            }
            mu = nextMu;
            delta = nextDelta;
            if (maxChange < RELABEL_EPSILON) {
                break;
            }
        }

        for (Map.Entry<String, Fact> entry : canonical.entrySet()) {
            Fact fact = entry.getValue();
            fact.setAttributes(formatLabels(mu.get(entry.getKey())));
            fact.setDeltaAttributes(formatLabels(delta.get(entry.getKey())));
        }
        // Per-rule intermediate facts (visible as graph nodes when aggregation occurred).
        for (Map.Entry<String, List<Derivation>> entry : derivations.entrySet()) {
            for (Derivation derivation : entry.getValue()) {
                Fact ruleFact = derivation.ruleFact();
                if (ruleFact == canonical.get(entry.getKey())) {
                    continue;
                }
                double[] support = supportFromWeakened(derivation, delta, labelCount);
                if (support != null) {
                    ruleFact.setAttributes(formatLabels(support));
                }
            }
        }
    }
}