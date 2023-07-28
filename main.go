package main

import (
	"bufio"
	"fmt"
	"image/color"
	"log"
	"math"
	"math/rand"
	"os"
	"sort"
	"strconv"
	"strings"
	"time"

	"gonum.org/v1/plot"
	"gonum.org/v1/plot/plotter"
	"gonum.org/v1/plot/vg"
)

type Parameters struct {
	VectorSize           int
	PopulationSize       int
	CrossoverProbability float64
	MutationProbability  float64
	AmountOfGenerations  int
	AttemptsCrossover    int
	AttemptsMutation     int
}

type MDNF struct {
	Vector          string
	GluedImplicants []string
	CoverTable      [][]bool
}

func Glue(table []string) []string {
	var glued []string
	used := make(map[string]struct{})
	gluedSet := make(map[string]struct{})

	sort.Strings(table)

	for {
		glued = []string{}
		for i := 0; i < len(table)-1; i++ {
			for j := i + 1; j < len(table); j++ {
				difference := CountDifference(table[i], table[j])
				if difference == 1 {
					glueResult := ChangeDifferent(table[i], table[j])
					if _, ok := used[glueResult]; !ok {
						gluedSet[table[i]] = struct{}{}
						gluedSet[table[j]] = struct{}{}
						used[glueResult] = struct{}{}
						glued = append(glued, glueResult)
					}
				}
			}
		}
		if len(glued) == 0 {
			break
		}
		for i := 0; i < len(table); i++ {
			if _, ok := gluedSet[table[i]]; !ok {
				glued = append(glued, table[i])
			}
		}
		table = glued
	}

	finalTable := make([]string, 0, len(table))
	for i := 0; i < len(table); i++ {
		if table[i] != "!" {
			finalTable = append(finalTable, table[i])
		}
	}

	return finalTable
}

func CountDifference(vector1 string, vector2 string) int {
	cnt := 0
	for i := 0; i < len(vector1); i++ {
		if vector1[i] != vector2[i] {
			cnt++
		}
	}
	return cnt
}

func ChangeDifferent(vector1 string, vector2 string) string {
	temp := []rune(vector1)
	for i := 0; i < len(vector1); i++ {
		if vector1[i] != vector2[i] {
			temp[i] = '*'
			break
		}
	}
	return string(temp)
}

func tableP(glued []string, table []string, tablePokr [][]bool) [][]bool {
	for i := 0; i < len(glued); i++ {
		for j := 0; j < len(table); j++ {
			cnt := 0
			temp1 := glued[i]
			temp2 := table[j]
			for k := 0; k < len(table[j]); k++ {
				if temp1[k] == temp2[k] || temp1[k] == '*' || temp2[k] == '*' {
					cnt++
				}
			}
			if cnt == len(table[j]) {
				tablePokr[i][j] = true
			}
		}
	}

	return tablePokr
}

func (m *MDNF) implicantCoveringMinterms(implicant string) map[int]bool {
	mintermsCovered := make(map[int]bool)
	for i, gluedImplicant := range m.GluedImplicants {
		if gluedImplicant == implicant {
			for minterm, isCovered := range m.CoverTable[i] {
				if isCovered {
					mintermsCovered[minterm] = true
				}
			}
			break
		}
	}
	return mintermsCovered
}

func (m *MDNF) generatePopulation(populationSize int) [][]string {
	population := make([][]string, populationSize)
	for i := 0; i < populationSize; i++ {
		var cover []string
		shuffledImplicants := make([]string, len(m.GluedImplicants))
		copy(shuffledImplicants, m.GluedImplicants)
		rand.Shuffle(len(shuffledImplicants), func(i, j int) {
			shuffledImplicants[i], shuffledImplicants[j] = shuffledImplicants[j], shuffledImplicants[i]
		})
		for _, implicant := range shuffledImplicants {
			if m.coversMissingMinterm(cover, implicant) {
				cover = append(cover, implicant)
			}
		}
		population[i] = cover
	}
	return population
}

func (m *MDNF) research(parent1, parent2 []string, probability float64, attempts int, table []string) ([]string, []string) {
	if rand.Float64() < probability {
		for i := 0; i < attempts; i++ {
			shortestLength := len(parent1)
			if len(parent2) < shortestLength {
				shortestLength = len(parent2)
			}
			crossOverPoint := rand.Intn(shortestLength)

			if crossOverPoint == 0 || crossOverPoint == len(parent1) {
				continue
			}

			child1 := append(append([]string{}, parent1[:crossOverPoint]...), parent2[crossOverPoint:]...)
			child2 := append(append([]string{}, parent2[:crossOverPoint]...), parent1[crossOverPoint:]...)

			child1 = m.repair(child1, table)
			child2 = m.repair(child2, table)

			return child1, child2
		}
	}

	return parent1, parent2
}

func (m *MDNF) coversMissingMinterm(cover []string, implicant string) bool {
	implicantMinterms := m.implicantCoveringMinterms(implicant)
	coverMinterms := m.coveredMinterms(cover)

	for minterm := range implicantMinterms {
		if !coverMinterms[minterm] {
			return true
		}
	}

	return false
}

func (m *MDNF) coveredMinterms(cover []string) map[int]bool {
	mintermsCovered := make(map[int]bool)
	for _, coverImplicant := range cover {
		for minterm := range m.implicantCoveringMinterms(coverImplicant) {
			mintermsCovered[minterm] = true
		}
	}
	return mintermsCovered
}

func (m *MDNF) mutate(individual []string, mutationRate float64, maxAttempts int) []string {
	randomFloat := rand.Float64()
	cnt := 0
	attempt := 0
	for cnt != 1 && attempt < maxAttempts {
		attempt++
		if randomFloat <= mutationRate {
			mutant := make([]string, len(individual))
			copy(mutant, individual)

			mutationBit := rand.Intn(len(mutant))
			mutationImplicant := []byte(mutant[mutationBit])

			mutationEl := rand.Intn(len(mutationImplicant))
			for mutationImplicant[mutationEl] == '*' {
				mutationEl = rand.Intn(len(mutationImplicant))
			}

			if mutationImplicant[mutationEl] == '1' {
				cnt++
				mutationImplicant[mutationEl] = '0'
			} else if mutationImplicant[mutationEl] == '0' {
				cnt++
				mutationImplicant[mutationEl] = '1'
			}

			if m.isValidCover(mutant) {
				fmt.Println("успешная мутация :", individual, " -> ", mutant)
				return mutant
			}
		}
	}
	return individual
}

func (m *MDNF) selectTopHalf(population [][]string) [][]string {
	sort.Slice(population, func(i, j int) bool {
		return len(population[i]) < len(population[j])
	})

	half := len(population) / 2
	population = population[:half]

	return population
}

func (m *MDNF) isValidCover(cover []string) bool {
	coveredMinterms := make(map[int]bool)
	for _, implicant := range cover {
		minterms := m.implicantCoveringMinterms(implicant)
		for minterm := range minterms {
			coveredMinterms[minterm] = true
		}
	}

	for i := 0; i < len(m.Vector); i++ {
		if m.Vector[i] == '1' && !coveredMinterms[i] {
			return false
		}
	}

	return true
}

func BestAndAverage(population [][]string) (best int, avg float64) {
	sum := 0
	mini := len(population[0])
	for i := 1; i < len(population); i++ {
		if len(population[i]) < mini {
			mini = len(population[i])
		}
		sum += len(population[i])
	}
	avg = float64(sum) / float64(len(population))
	return mini, avg
}

func plotGraph(bestFitnesses []int, averageFitnesses []float64, title string) {
	p := plot.New()

	p.Title.Text = title
	p.X.Label.Text = "Итерация(Эпоха)"
	p.Y.Label.Text = "Количество литерал в МДНФ"

	bestPts := make(plotter.XYs, len(bestFitnesses))
	for i := range bestPts {
		bestPts[i].X = float64(i)
		bestPts[i].Y = float64(bestFitnesses[i])
	}

	avgPts := make(plotter.XYs, len(averageFitnesses))
	for i := range avgPts {
		avgPts[i].X = float64(i)
		avgPts[i].Y = averageFitnesses[i]
	}

	bestLine, err := plotter.NewLine(bestPts)
	if err != nil {
		log.Fatal(err)
	}

	avgLine, err := plotter.NewLine(avgPts)
	if err != nil {
		log.Fatal(err)
	}

	bestLine.Color = color.RGBA{B: 0, A: 255}
	bestLine.Width = vg.Points(2)

	avgLine.Color = color.RGBA{R: 255, A: 255}
	avgLine.Width = vg.Points(2)

	p.Add(bestLine, avgLine)

	p.Legend.Add("Лучшее решение пчелы-собирателя", bestLine)
	p.Legend.Add("Среднее решение пчелы-собирателя", avgLine)

	if err := p.Save(10*vg.Inch, 6*vg.Inch, title+".png"); err != nil {
		log.Fatal(err)
	}
}

type Cover []string

func (c Cover) Contains(s string) bool {
	for _, el := range c {
		if el == s {
			return true
		}
	}
	return false
}

func (m *MDNF) isCovered(minterm string, child []string) bool {
	for _, term := range child {
		if m.isCoveredByMinterm(term, minterm) {
			return true
		}
	}
	return false
}

func (m *MDNF) isCoveredByMinterm(term string, minterm string) bool {
	if len(term) < len(minterm) {
		term += strings.Repeat("*", len(minterm)-len(term))
	}
	for i, char := range minterm {
		if char != '*' && char != rune(term[i]) {
			return false
		}
	}
	return true
}


func (m *MDNF) repair(child []string, table []string) []string {
	childMap := make(map[string]bool)
	for _, term := range child {
		childMap[term] = true
	}

	for _, minterm := range table {
		if !m.isCovered(minterm, child) {
			for _, term := range table {
				if m.isCoveredByMinterm(term, minterm) && !childMap[term] {
					child = append(child, term)
					childMap[term] = true
					break
				}
			}
		}
	}
	return child
}


func main() {
	rand.Seed(time.Now().UnixNano())

	file0, err := os.Open("function.txt")
	if err != nil {
		log.Fatal(err)
	}
	defer file0.Close()

	var vector string
	scanner0 := bufio.NewScanner(file0)
	for scanner0.Scan() {
		vector = scanner0.Text()
	}

	fmt.Println(vector)

	file1, err := os.Open("parameters.txt")
	if err != nil {
		log.Fatal(err)
	}
	defer file1.Close()

	params := Parameters{}
	scanner := bufio.NewScanner(file1)
	for scanner.Scan() {
		line := scanner.Text()
		parts := strings.Split(line, ": ")
		if len(parts) != 2 {
			log.Fatal("Invalid line: ", line)
		}
		switch parts[0] {
		case "количество пчел-собирателей":
			params.PopulationSize, err = strconv.Atoi(parts[1])
			if err != nil {
				log.Fatal(err)
			}
		case "количество пчел-разведчиков":
			params.CrossoverProbability, err = strconv.ParseFloat(parts[1], 64)
			if err != nil {
				log.Fatal(err)
			}
		case "количество итераций":
			params.AmountOfGenerations, err = strconv.Atoi(parts[1])
			if err != nil {
				log.Fatal(err)
			}
		}
	}

	params.MutationProbability = 1

	temor := params.CrossoverProbability

	if temor >= 1 && temor < 10 {
		params.CrossoverProbability *= 98
	}
	if temor >= 10 && temor < 100 {
		params.CrossoverProbability *= 95
	}
	if temor >= 100 && temor < 1000 {
		params.CrossoverProbability *= 92
	}
	if temor >= 1000 && temor < 10000 {
		params.CrossoverProbability *= 90
	}
	if temor >= 1000 && temor < 10000 {
		params.CrossoverProbability *= 89
	}
	if temor >= 10000 {
		params.CrossoverProbability *= 85
	}

	for params.CrossoverProbability >= 1 {
		params.CrossoverProbability /= 10
	}

	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	var table []string
	var n = math.Log2(float64(len(vector)))

	for i := 0; i < len(vector); i++ {
		temp := fmt.Sprintf("%b", i)
		for ; float64(len(temp)) < n; {
			temp = "0" + temp
		}
		if vector[i] == '1' {
			table = append(table, temp)
		}
	}

	gluedParts := Glue(table)
	fmt.Println("finalTable :", gluedParts)

	tablePokr := make([][]bool, len(gluedParts))

	for i := range tablePokr {
		tablePokr[i] = make([]bool, len(table))
	}

	tablePokr = tableP(gluedParts, table, tablePokr)

	m := MDNF{
		Vector:          vector,
		GluedImplicants: gluedParts,
		CoverTable:      tablePokr,
	}

	population := m.generatePopulation(params.PopulationSize)
	fmt.Println("Изначальные пчелы:")
	for i, cover := range population {
		fmt.Printf("Покрытие %d: %v\n", i, cover)
	}

	bestLen := make([]int, params.AmountOfGenerations)
	avgLen := make([]float64, params.AmountOfGenerations)

	for gen := 0; gen < params.AmountOfGenerations; gen++ {

		fmt.Println("Итерация:", gen)

		for i := 0; i < params.PopulationSize-1; i += 2 {
			temp := rand.Intn(len(population))
			child1, child2 := m.research(population[i], population[temp], params.CrossoverProbability, 1000, table)
			population = append(population, child1, child2)
		}

		for i := 0; i < params.PopulationSize; i++ {
			population[i] = m.mutate(population[i], params.MutationProbability, 1000)
		}

		population = m.selectTopHalf(population)

		best, avg := BestAndAverage(population)
		bestLen[gen] = best
		avgLen[gen] = avg

		fmt.Println("Лучшее решение пчелы-собирателя:", best)
		fmt.Println("Среднее решение пчелы-собирателя", avg)
		fmt.Println()
	}

	plotGraph(bestLen, avgLen, "График зависимости итерации от количества импликант")
	fmt.Println(population[0])
	fmt.Println("Нажмите Enter для закрытия консоли...")
	_, err5 := bufio.NewReader(os.Stdin).ReadBytes('\n')
	if err5 != nil {
		return
	}
}

