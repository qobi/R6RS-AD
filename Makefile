src=$(wildcard *.ss)

TAGS: $(src)
	etags --language=scheme --regex="/[ \t]*(def[a-z-]+[ \t]+(.*)/1/" $^
