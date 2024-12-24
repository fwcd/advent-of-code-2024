package main

import (
	"fmt"
	"os"
	"strings"
)

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
	graph := make(map[string][]string)
	for _, line := range input {
		split := strings.Split(line, "-")
		if len(split) >= 2 {
			graph[split[0]] = append(graph[split[0]], split[1])
		}
	}
	fmt.Println(graph)
}
