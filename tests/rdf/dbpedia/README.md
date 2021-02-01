dbpedia - download and convert to TML

	- un/comment urls in _urllist_ file to specify files to download
	- run _download.sh_ to download and decompress dbpedia files
	- optionally edit _convert.sh_ to update path to TML executable (defaults to ../../../build-Release/tml)
	- run _convert.sh_ to convert decompressed dbpedia files to TML (takes optional argument: number of records converted from original ntriples file, defaults to 1000 lines)

RDF ntriples conversion into TML:

	- IRIs are converted to strings
	- RDF statement triple is stored in _rdf(?subject ?predicate ?object)_
	- literals are converted into _literal(?value ?type)_
	- langStrings are converted into _langString(?string ?langCode)_
	- http://www.w3.org/2001/XMLSchema#byte / short / int literals are kept as native TML number (note: http://www.w3.org/2001/XMLSchema#integer is not limited by bitsize and thus is not converted into TML native)

