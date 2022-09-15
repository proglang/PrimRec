PREFIX= latex
TARGET_MODULES= PR-Nat PR-Words NatsToWords NatsVec-CC PR-CC PR-Nat-Example PR-NatsVec Utils
TARGET_BROKEN=  PrimRecWord
TARGET_FILES= $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))

.PHONY: all all_files

all:
	pdflatex jfpmain

all_files: $(TARGET_FILES)
	@echo $(PATH)

$(PREFIX)/%.tex: %.lagda
	agda --latex $<
