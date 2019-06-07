echo "Model Variables: parameters and assumptions on them"
grep "Axiom\|Parameter" -r * --include *.v | wc -l
echo -e "\nDefinitions: functions, relations, abbreviations"
grep "Inductive\|Definition\|Fixpoint\|Notation" -r * --include *.v | wc -l
echo -e "\nResults: theorems, lemmas, propositions, corollaries"
grep "Theorem\|Lemma\|Proposition\|Corollary" -r * --include *.v | wc -l
echo -e "\nAdmitted results"
grep "Admitted" -r * --include *.v | wc -l
echo -en "\nTOTAL\nLINES: "
find . -name '*.v' | xargs cat | wc -l
echo -n "BYTES: "
find . -name '*.v' | xargs cat | wc -c

