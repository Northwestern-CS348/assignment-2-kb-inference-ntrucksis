import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument
        Args:
            fact (Fact): Fact we're searching for
        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument
        Args:
            rule (Rule): Rule we're searching for
        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB
        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB
        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)
        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB
        Args:
            fact (Fact) - Fact to be retracted
        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])

        # if fact is unsupported, retract it from all of the facts and rules that it
        # supported and remove the fact from the Knowledge Base
        
        if isinstance(fact_or_rule, Fact): 
            if fact_or_rule in self.facts: 
                fact = self._get_fact(fact_or_rule) 
                if not fact.supported_by:
                    for supporting in fact.supported_by:
                        for i in supporting:
                            i.supports_facts.remove(fact)
                    for supported_fact in fact.supports_facts:
                        supported_fact.supported_by = [x for x in supported_fact.supported_by if x[0]!=fact]
                        self.kb_retract(supported_fact) 
                    for supported_rule in fact.supports_rules:
                        supported_rule.supported_by = [x for x in supported_rule.supported_by if x[0]!=fact]
                        self.kb_retract(supported_rule) 
                    self.facts.remove(fact) 

        # if rule is not an asserted rule, remove the rule from all of the facts and rules that support it
        # and retract the rule from all facts and rules that it supported
        
        elif isinstance(fact_or_rule, Rule): 
            if fact_or_rule in self.facts: 
                rule = self._get_rule(fact_or_rule) 
                if not ruleRetract.asserted: 
                    for supporting in rule.supported_by:
                        for i in supporting:
                            i.supports_rules.remove(rule) 
                    for supported_rule in rule.supports_rules:
                        supported_rule.supported_by = [x for x in supported_rule.supported_by if x[1]!=rule]
                        self.kb_retract(supported_rule)
                    for supported_fact in rule.supports_facts:
                        supported_fact.supported_by = [x for x in supported_fact.supported_by if x[1]!=rule]
                        self.kb_retract(supported_fact) 
                    self.rules.remove(rule)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules
        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase
        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])

        bindings = match(fact.statement, rule.lhs[0])
        if bindings:
            # if multiple statements on LHS, make new RHS and LHS 
            # connect supporting facts and rules to the new rule
            if len(rule.lhs) > 1:
                new_rhs = instantiate(rule.rhs, bindings)
                new_lhs = [instantiate(i, bindings) for i in rule.lhs[1:]]
                new_rule = Rule([new_lhs, new_rhs], [[fact, rule]])
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_assert(new_rule)

            # if there isn't multiple statements on LHS, add 
            # a new fact to infer and update supporting facts and rules
            else:
                new_rhs = instantiate(rule.rhs, bindings)
                new_fact = Fact(new_rhs, [[fact, rule]])
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                kb.kb_assert(new_fact)
        return
