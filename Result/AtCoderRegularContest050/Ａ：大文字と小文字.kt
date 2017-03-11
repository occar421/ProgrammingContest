import java.util.Scanner
 
fun main(args: Array<String>) {
	var sc = Scanner(System.`in`)
 
	val l = sc.next()
	val s = sc.next()
 
	println(if (l == s.toUpperCase()) "Yes" else "No")
}