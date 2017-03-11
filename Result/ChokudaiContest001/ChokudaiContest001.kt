import java.util.Scanner
 
fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)
 
	val field = Array(30, { Array(30, { sc.nextInt() }).toMutableList() }).toList()
 
 
	// fool program
	while (true) {
		// pick a max
		val most = field.mapIndexed { i, a ->
			val g = a.mapIndexed { j, v ->
				Triple(j, v, field.getNeighbors(i, j).sumBy { it.third } + v)
			}.groupBy { it.second }.maxBy { it.key }!!
 
			Pair(i, if (g.key == 0) Triple(-1, -1, 0) else g.value.maxBy { it.third }!!)
		}.maxBy { it.second.third }!!
 
		if (most.second.second <= 0) {
			break;
		}
 
		var i = most.first
		var j = most.second.first
		do {
			println("${i + 1} ${j + 1}")
 
			field[i][j]--
 
			val list = field.getNeighbors(i, j)
			val m = list.maxBy { it.third }!!
			i = m.first
			j = m.second
		} while (m.third > 0)
	}
}
 
fun List<MutableList<Int>>.getNeighbors(i: Int, j: Int): List<Triple<Int, Int, Int>> {
	val list = mutableListOf<Triple<Int, Int, Int>>()
	if (i != 0) {
		list.add(Triple(i - 1, j, this[i - 1][j]))
	}
	if (i != 29) {
		list.add(Triple(i + 1, j, this[i + 1][j]))
	}
	if (j != 0) {
		list.add(Triple(i, j - 1, this[i][j - 1]))
	}
	if (j != 29) {
		list.add(Triple(i, j + 1, this[i][j + 1]))
	}
	return list
}