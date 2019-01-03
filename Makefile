AGDA=agda
AFLAGS=-i./$(AGDA_DIR)

AGDA_DIR=agda
HTML_DIR=html

ROOT=$(AGDA_DIR)/Index.agda
SOURCES=$(shell find $(AGDA_DIR)/ -maxdepth 1 \( -name '*.agda' -or -name '*.lagda' \) -and -not -wholename $(ROOT))

all: clean $(ROOT) $(HTML_DIR)

$(ROOT): $(ROOT).tmpl $(SOURCES)
	cp $@.tmpl $@
	echo $(SOURCES) | \
		xargs basename --suffix=.agda | \
		xargs basename --suffix=.lagda | \
		xargs -I '{}' echo 'import {}' >> $@

$(HTML_DIR): $(ROOT)
	$(AGDA) $(AFLAGS) --html $(ROOT) --html-dir $(HTML_DIR)

clean:
	rm -rf $(HTML_DIR)
	rm -f $(ROOT)
	find $(AGDA_DIR)/ -name '*.agdai' -delete

.PHONY: all clean
