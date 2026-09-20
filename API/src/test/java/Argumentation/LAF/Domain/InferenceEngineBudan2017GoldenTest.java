package Argumentation.LAF.Domain;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import Argumentation.LAF.Service.InferenceService;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Test;

/** Casos dorados del perfil de confianza y preferencia usado por el TFG. */
class InferenceEngineBudan2017GoldenTest {

    private static final double EPSILON = 0.000001;

    @Test
    void supportPropagatesConfidenceAndPreference() {
        Fact evidence = fact("evidence", "productA", 0.5, 0.8);
        Rule conclusion = rule("recommend", "evidence", 0.4, 1.0);

        ArgumentativeGraph graph = build(List.of(evidence), List.of(conclusion));
        Fact result = terminalFact(graph, "recommend", "productA");

        // Confianza: 0.5 * 0.4 = 0.2. Preferencia: min(0.8, 1) = 0.8.
        assertLabels(result.getAttributes(), 0.2, 0.8);
    }

    @Test
    void aggregationCombinesIndependentSupport() {
        List<Fact> facts = List.of(
                fact("quality", "productA", 0.3, 0.7),
                fact("delivery", "productA", 0.4, 0.6));
        List<Rule> rules = List.of(
                rule("recommend", "quality", 1.0, 1.0),
                rule("recommend", "delivery", 1.0, 1.0));

        Fact result = terminalFact(build(facts, rules), "recommend", "productA");

        // Confianza: 0.3 + 0.4 - 0.3*0.4 = 0.58.
        // Preferencia: min(0.7 + 0.6, 1) = 1.
        assertLabels(result.getAttributes(), 0.58, 1.0);
    }

    @Test
    void conflictWeakensBothSidesWithTheConfiguredDifference() {
        Fact positive = fact("recommend", "productA", 0.8, 0.7);
        Fact negative = fact("~recommend", "productA", 0.5, 0.2);

        ArgumentativeGraph graph = build(List.of(positive, negative), List.of());
        PairInConflict conflict = graph.conflictiveNodes().getFirst();
        Fact weakenedPositive = "recommend".equals(conflict.first().getName())
                ? conflict.first() : conflict.second();
        Fact weakenedNegative = "~recommend".equals(conflict.first().getName())
                ? conflict.first() : conflict.second();

        // Confianza positiva: (0.8-0.5)/(1-0.5) = 0.6.
        // Preferencia positiva: max(0.7-0.2, 0) = 0.5.
        assertLabels(weakenedPositive.getDeltaAttributes(), 0.6, 0.5);
        assertLabels(weakenedNegative.getDeltaAttributes(), 0.0, 0.0);
    }

    @Test
    void conflictTieAtOneIsFiniteAndSymmetric() {
        Fact positive = fact("recommend", "productA", 1.0, 1.0);
        Fact negative = fact("~recommend", "productA", 1.0, 1.0);

        PairInConflict conflict = build(
                List.of(positive, negative),
                List.of()).conflictiveNodes().getFirst();

        for (Fact side : List.of(conflict.first(), conflict.second())) {
            assertLabels(side.getDeltaAttributes(), 0.0, 0.0);
            assertTrue(Double.isFinite(Double.parseDouble(side.getDeltaAttributes()[0])));
            assertTrue(Double.isFinite(Double.parseDouble(side.getDeltaAttributes()[1])));
        }
    }

    @Test
    void laf1ChainRanksProductsByConservativeProjection() {
        List<Fact> facts = List.of(
                fact("positiveTasteReview", "productA", 0.8, 0.9),
                fact("positiveTasteReview", "productB", 0.7, 1.0));
        List<Rule> rules = List.of(
                rule("tasteGood", "positiveTasteReview", 1.0, 1.0),
                rule("recommend", "tasteGood", 1.0, 1.0));

        ArgumentativeGraph graph = build(facts, rules);
        Fact productA = terminalFact(graph, "recommend", "productA");
        Fact productB = terminalFact(graph, "recommend", "productB");

        assertLabels(productA.getDeltaAttributes(), 0.8, 0.9);
        assertLabels(productB.getDeltaAttributes(), 0.7, 1.0);
        assertTrue(conservativeScore(productA) > conservativeScore(productB));
    }

    @Test
    void laf2ChainAggregatesPurchaseConditionsAndRanksListings() {
        List<Fact> facts = List.of(
                fact("goodPrice", "itemA", 0.95, 1.0),
                fact("freeShipping", "itemA", 0.95, 0.5),
                fact("goodPrice", "itemB", 0.7, 1.0));
        List<Rule> rules = List.of(
                rule("goodPurchase", "goodPrice", 1.0, 1.0),
                rule("goodPurchase", "freeShipping", 1.0, 1.0),
                rule("recommend", "goodPurchase", 1.0, 1.0));

        ArgumentativeGraph graph = build(facts, rules);
        Fact itemA = terminalFact(graph, "recommend", "itemA");
        Fact itemB = terminalFact(graph, "recommend", "itemB");

        assertLabels(itemA.getDeltaAttributes(), 0.9975, 1.0);
        assertLabels(itemB.getDeltaAttributes(), 0.7, 1.0);
        assertTrue(conservativeScore(itemA) > conservativeScore(itemB));
    }

    private ArgumentativeGraph build(List<Fact> facts, List<Rule> rules) {
        return new InferenceService().buildGraph(
                new ArrayList<>(facts),
                rules,
                budan2017Operations());
    }

    private Map<String, OperationSet> budan2017Operations() {
        Map<String, OperationSet> operations = new LinkedHashMap<>();
        operations.put(
                "confidence",
                new OperationSet(
                        "X * Y",
                        "X + Y - X * Y",
                        "max((X-Y)/max(1-Y,0.000000001),0)"));
        operations.put(
                "preference",
                new OperationSet(
                        "min(X,Y)",
                        "min(X+Y,1)",
                        "max(X-Y,0)"));
        return operations;
    }

    private Fact fact(String name, String argument, double confidence, double preference) {
        return new Fact(
                name,
                argument,
                new String[] { String.valueOf(confidence), String.valueOf(preference) });
    }

    private Rule rule(String head, String body, double confidence, double preference) {
        return new Rule(
                head,
                List.of(body),
                new String[] { String.valueOf(confidence), String.valueOf(preference) });
    }

    private Fact terminalFact(ArgumentativeGraph graph, String name, String argument) {
        Set<KnowledgePiece> superseded = new HashSet<>(graph.edges().keySet());
        return graph.edges().values().stream()
                .flatMap(List::stream)
                .filter(fact -> name.equals(fact.getName()))
                .filter(fact -> argument.equals(fact.getArgument()))
                .filter(fact -> !superseded.contains(fact))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        "No se derivó " + name + "(" + argument + ")"));
    }

    private double conservativeScore(Fact fact) {
        return Math.min(
                Double.parseDouble(fact.getDeltaAttributes()[0]),
                Double.parseDouble(fact.getDeltaAttributes()[1]));
    }

    private void assertLabels(String[] labels, double confidence, double preference) {
        assertEquals(confidence, Double.parseDouble(labels[0]), EPSILON);
        assertEquals(preference, Double.parseDouble(labels[1]), EPSILON);
    }
}
