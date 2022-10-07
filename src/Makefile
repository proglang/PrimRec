PREFIX= latex
TARGET_MODULES= PR-Nat PR-Words PR-Trees PR-HTrees NatsToWords WordsToTrees TreesToHTrees NatsVec-CC PR-CC PR-Nat-Example PR-Trees-Examples PR-NatsVec Utils System-T0 EvalPConstructor VecProperties PR-SystemT0-Embedding System-T0-PR-Embedding PR-CC-ind
TARGET_BROKEN=  PrimRecWord
TARGET_FILES= $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))

.PHONY: all all_files

all: all_files
	pdflatex jfpmain

all_files: $(TARGET_FILES)
	@echo $(PATH)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<
