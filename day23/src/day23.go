package main

import (
	"fmt"
	"os"
	"strings"
)

type Graph = map[string]map[string]bool

func threeCliques(graph Graph, prefix string) int {
	nodes := make([]string, len(graph))
	i := 0
	for n := range graph {
		nodes[i] = n
		i++
	}

	cliques := 0
	for i1, n1 := range nodes {
		for i2, n2 := range nodes[i1+1:] {
			for _, n3 := range nodes[i1+i2+1:] {
				es1 := graph[n1]
				es2 := graph[n2]
				es3 := graph[n3]
				if es1[n2] && es1[n3] && es2[n1] && es2[n3] && es3[n1] && es3[n2] {
					// We have a 3-clique
					if strings.HasPrefix(n1, prefix) || strings.HasPrefix(n2, prefix) || strings.HasPrefix(n3, prefix) {
						cliques++
					}
				}
			}
		}
	}
	return cliques
}

func addEdge(graph Graph, n1 string, n2 string) {
	es, ok := graph[n1]
	if !ok {
		es = make(map[string]bool)
		graph[n1] = es
	}
	es[n2] = true
}

func main() {
	args := os.Args
	if len(args) <= 1 {
		fmt.Println("usage:", args[0], "<path to input>")
		os.Exit(1)
	}

	data, err := os.ReadFile(args[1])
	if err != nil {
		panic(err)
	}

	input := strings.Split(string(data), "\n")
	graph := make(Graph)
	for _, line := range input {
		split := strings.Split(line, "-")
		if len(split) >= 2 {
			addEdge(graph, split[0], split[1])
			addEdge(graph, split[1], split[0])
		}
	}
	fmt.Println("Part 1:", threeCliques(graph, "t"))

	// Part 2 was solved by inspecting the output in GraphViz:
	//
	//     scripts/dotify resources/input.txt | neato -Tpdf -o <path/to/output.pdf>
	//
	// The clique can be found at the very top.
}
