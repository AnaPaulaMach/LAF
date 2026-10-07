package Argumentation.LAF.Domain;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.Test;

/**
 * Propagación con premisas debilitadas (Budán et al. 2017, Def. 8(iii) y Algoritmo 2):
 * el soporte de una conclusión usa δ de sus premisas, no μ. Los casos cubren lo que
 * {@link InferenceEngineBudan2017GoldenTest} no cubría: una premisa intermedia contradicha
 * seguida de una regla.
 */
class InferenceEngineWeakenedPropagationTest {

    private static final double EPSILON = 1e-9;

    private static final String[][] CONFIDENCE_ALGEBRA = {
            { "X * Y", "X + Y - X * Y", "max((X-Y)/max(1-Y,0.000000001),0)" }
    };

    /** Control sintético del 30/09/2026 (verificacion_semantica_minima_20260930.json). */
    private static List<Fact> syntheticFacts() {
        return new ArrayList<>(List.of(
                new Fact("sabor", "p", new String[] { "0.8" }),
                new Fact("~sabor", "p", new String[] { "0.6" })));
    }

    private static List<Rule> syntheticRules() {
        return List.of(
                new Rule("recomendar", List.of("sabor"), new String[] { "0.9" }),
                new Rule("~recomendar", List.of("~sabor"), new String[] { "0.9" }));
    }

    @Test
    void weakenedPremiseFeedsTheNextRule() {
        InferenceEngine engine = new InferenceEngine(syntheticFacts(), syntheticRules(), CONFIDENCE_ALGEBRA, true);
        ArgumentativeGraph graph = engine.buildTree();
        Map<String, Fact> facts = byLiteral(graph);

        assertLabel(facts.get("sabor(p)"), 0.8, 0.5);
        assertLabel(facts.get("~sabor(p)"), 0.6, 0.0);
        // Def. 8(iii): mu_recomendar = delta_sabor (0.5) * 0.9 = 0.45; mu_~recomendar = 0 * 0.9 = 0.
        assertLabel(facts.get("recomendar(p)"), 0.45, 0.45);
        assertLabel(facts.get("~recomendar(p)"), 0.0, 0.0);
        assertTrue(engine.isPropagateWeakened());
    }

    @Test
    void legacyModeStillPropagatesAccruedValues() {
        InferenceEngine engine = new InferenceEngine(syntheticFacts(), syntheticRules(), CONFIDENCE_ALGEBRA, false);
        Map<String, Fact> facts = byLiteral(engine.buildTree());

        // Comportamiento histórico del motor: 0.8*0.9 = 0.72, 0.6*0.9 = 0.54, (0.72-0.54)/(1-0.54).
        assertLabel(facts.get("recomendar(p)"), 0.72, 0.18 / 0.46);
        assertLabel(facts.get("~recomendar(p)"), 0.54, 0.0);
        assertFalse(engine.isPropagateWeakened());
    }

    @Test
    void threeLevelChainMatchesTheArticleRecurrence() {
        // Cadena de producción (programas_por_aspecto/sabor.txt) con los valores de Blasón Espresso Robusto.
        List<Fact> facts = new ArrayList<>(List.of(
                new Fact("resenaPositivaSabor", "blason", new String[] { "0.94" }),
                new Fact("resenaNegativaSabor", "blason", new String[] { "0.06" })));
        List<Rule> rules = List.of(
                new Rule("saborBueno", List.of("resenaPositivaSabor"), new String[] { "0.85" }),
                new Rule("~saborBueno", List.of("resenaNegativaSabor"), new String[] { "0.85" }),
                new Rule("sensorialBueno", List.of("saborBueno"), new String[] { "0.90" }),
                new Rule("~sensorialBueno", List.of("~saborBueno"), new String[] { "0.92" }),
                new Rule("recomendar", List.of("sensorialBueno"), new String[] { "0.90" }),
                new Rule("~recomendar", List.of("~sensorialBueno"), new String[] { "0.92" }));

        Map<String, Fact> result = byLiteral(new InferenceEngine(facts, rules, CONFIDENCE_ALGEBRA, true).buildTree());

        double muSabor = 0.94 * 0.85;                 // 0.799
        double muNoSabor = 0.06 * 0.85;               // 0.051
        double deltaSabor = (muSabor - muNoSabor) / (1 - muNoSabor);
        assertLabel(result.get("saborBueno(blason)"), muSabor, deltaSabor);
        assertLabel(result.get("~saborBueno(blason)"), muNoSabor, 0.0);
        assertLabel(result.get("sensorialBueno(blason)"), deltaSabor * 0.90, deltaSabor * 0.90);
        assertLabel(result.get("~sensorialBueno(blason)"), 0.0, 0.0);
        assertLabel(result.get("recomendar(blason)"), deltaSabor * 0.81, deltaSabor * 0.81); // 0.6384404636
    }

    @Test
    void programFactThatIsAlsoDerivedAggregatesItsOwnLabel() {
        // Def. 8(iii), caso X en K: mu = F(X) (+) soporte de las reglas.
        List<Fact> facts = new ArrayList<>(List.of(
                new Fact("a", "x", new String[] { "0.5" }),
                new Fact("b", "x", new String[] { "0.3" })));
        List<Rule> rules = List.of(new Rule("b", List.of("a"), new String[] { "1.0" }));

        Map<String, Fact> result = byLiteral(new InferenceEngine(facts, rules, CONFIDENCE_ALGEBRA, true).buildTree());

        // 0.5 (+) 0.3 = 0.5 + 0.3 - 0.15 = 0.65
        assertLabel(result.get("b(x)"), 0.65, 0.65);
    }

    @Test
    void conflictFreeChainIsUnchangedByTheMode() {
        List<Fact> facts = new ArrayList<>(List.of(new Fact("evidence", "p", new String[] { "0.5" })));
        List<Rule> rules = List.of(
                new Rule("aspect", List.of("evidence"), new String[] { "0.8" }),
                new Rule("recommend", List.of("aspect"), new String[] { "0.5" }));

        Map<String, Fact> weakened = byLiteral(new InferenceEngine(copy(facts), rules, CONFIDENCE_ALGEBRA, true).buildTree());
        Map<String, Fact> accrued = byLiteral(new InferenceEngine(copy(facts), rules, CONFIDENCE_ALGEBRA, false).buildTree());

        assertLabel(weakened.get("recommend(p)"), 0.2, 0.2);
        assertLabel(accrued.get("recommend(p)"), 0.2, 0.2);
    }

    private static List<Fact> copy(List<Fact> facts) {
        List<Fact> copies = new ArrayList<>();
        for (Fact fact : facts) {
            copies.add(new Fact(fact.getName(), fact.getArgument(), fact.getAttributes().clone()));
        }
        return copies;
    }

    private static Map<String, Fact> byLiteral(ArgumentativeGraph graph) {
        Map<String, Fact> facts = new java.util.LinkedHashMap<>();
        java.util.Set<KnowledgePiece> parents = graph.edges().keySet();
        for (List<Fact> children : graph.edges().values()) {
            for (Fact child : children) {
                if (!parents.contains(child)) { // terminal version of the literal
                    facts.put(child.getName() + "(" + child.getArgument() + ")", child);
                }
            }
        }
        for (KnowledgePiece parent : parents) {
            if (parent instanceof Fact fact) {
                facts.putIfAbsent(fact.getName() + "(" + fact.getArgument() + ")", fact);
            }
        }
        for (PairInConflict pair : graph.conflictiveNodes()) {
            facts.put(pair.first().getName() + "(" + pair.first().getArgument() + ")", pair.first());
            facts.put(pair.second().getName() + "(" + pair.second().getArgument() + ")", pair.second());
        }
        return facts;
    }

    private static void assertLabel(Fact fact, double mu, double delta) {
        assertEquals(mu, Double.parseDouble(fact.getAttributes()[0]), EPSILON, "mu de " + fact);
        assertEquals(delta, Double.parseDouble(fact.getDeltaAttributes()[0]), EPSILON, "delta de " + fact);
    }
}
