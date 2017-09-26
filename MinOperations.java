/**
 *  Author: Yuqi Huang
 *  Date: 9/25/2017
 *  Version: Java8
 *  
 *  Description: Using a modified version of Astar search algorithm
 *  to find shortest path that lead to the target from origin string,
 *  where levenshtein distance is usded as the heuristic function(estimation function).
 *  For each state of the current word, generate all possible children by add, delete,
 *  change and anagram. PriorityQueue are used as the fronter to store all valid childs 
 *  and a HaspMap is used to store all the explored children.
 *  
 */
import java.util.*;
import java.io.IOException;
import java.lang.reflect.Array;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

/**
 *  a subclass for constructing the stringValuepair object 
 *  used for A* algorithm. 
 */
class StringValuePair {
    private String str;
    private int cost;
    private int heur; // estimate function
    public StringValuePair(String str, int cost, int heur){
        this.str = str;
        this.cost = cost;
        this.heur = heur;
    }
    public String getStr(){
        return this.str;
    }
    public void updateCost(int cost){
        this.cost = cost;
    }
    public int getCost(){
        return this.cost;
    }
    public void updateHeur(int heuristic){
        this.heur = heuristic;
    }
    public int getHeur(){
        return this.heur;
    }
}

public class MinOperations{
    // Hashset to store all dictionary words
    private Set<String> wordsSet = new HashSet<>();
    // four operations specified by the puzzle
    // 1. add;  2.delete; 3.change;  4.anagram;
    private int[] operations = new int[4];
    private String origin;
    private String target;
    private String wordFile = "words.txt";
    private int maxWordLen = 0;
    // hashMap to store anagrams for given charaters, 
    // key: string formed by sorted characters, List: all string with same characters
    private HashMap<String, List<String>> anagrams = new HashMap() ;
    

    // main method for testing the algorithm
    public static void main(String[] args){
        
        Scanner scr = new Scanner(System.in);
        System.out.print("Enter fileName or type exit for stop: ");
        String next = scr.nextLine().trim().toLowerCase();
        while(!next.equals("exit")){
            MinOperations test1 = new MinOperations(next);
            System.out.println("cost from " + test1.getStart() + " to " + 
            test1.getTarget() + " is " + test1.findMin(test1.getStart(), test1.getTarget()));
            System.out.print("Enter fileName or type exit for stop: ");
            next = scr.nextLine().trim().toLowerCase();
        }
    }

    // default constructor to load instruction from provided filePath
    public MinOperations(String filePath){
        this.readInstruction(filePath);
        this.loadDictionary(this.wordFile);
        this.creatAnagramTable();
    }
    
    // second constructor, reads instruction from manual inputs 
    public MinOperations(int[] operations, String origin, String target){
        this.operations =  operations;
        this.origin = origin.trim().toLowerCase();
        this.target = target.trim().toLowerCase();
        this.loadDictionary(this.wordFile);
        this.creatAnagramTable();
    }

    public int findMin(String origin, String target) {
        // if the target/origin words are not valid words;
        if(!this.isWord(target) || !this.isWord(origin)) return -1;

        // store all the explored string and corresponding cost
        HashMap<String, Integer> explored = new HashMap<String, Integer>();

        findMinAstar(origin, target, explored); 
        if(explored.containsKey(target)){
            return explored.get(target);
        }else {
            return -1;
        }
    }

    /**
     *  core algorithm for finding the min cost using A* search and Levendistance as the heuristic function
     */
    private void findMinAstar(String source, String target, HashMap<String, Integer> explored){

        // use priorityQueue to store all valid children, sorted by (currentCost + levenshteinDistance)
        PriorityQueue<StringValuePair> fronter = new PriorityQueue<StringValuePair>(20, (a, b)->a.getHeur() - b.getHeur());

        fronter.offer(new StringValuePair(source, 0, this.LD(source, target)));
        StringValuePair curPair;
        while(fronter.peek() != null){
            curPair = fronter.poll();
            // expand the fronter with all valid children
            String cur = curPair.getStr();
            String buff;
            int cost = curPair.getCost();
            if(!explored.containsKey(cur) || explored.get(cur) > cost) {
                explored.put(cur, cost);
            }
            // populate all potential children from the current states from four operations
            // add
            int addCost = cost + this.addCost();
            for(int i = 0; i <= cur.length(); i++){
                for(int j = 0; j < 26; j++){
                    buff = this.add(i, cur, (char)(j + 'a'));
                    if(this.checkValid(buff, target, addCost, explored)){
                        StringValuePair temp = new StringValuePair(buff, addCost, addCost + this.LD(buff, target));
                        this.addToFronter(fronter, temp, explored);
                    }
                }
            }
            // delete 
            int deleteCost = cost + this.deleteCost();
            for(int i = 0; i < cur.length(); i++){
                 buff = this.delete(i, cur);
                 if(this.checkValid(buff, target, deleteCost, explored)){
                     StringValuePair temp = new StringValuePair(buff, deleteCost, deleteCost + this.LD(buff, target));
                     this.addToFronter(fronter, temp, explored);
                 }
            }
            // change
            int changeCost = cost + this.changeCost();
            for(int i = 0; i < cur.length(); i++){
                for(int j = 0; j < 26; j++){
                    buff = this.change(cur, i, (char)(j + 'a'));
                    if(this.checkValid(buff, target, changeCost, explored)){
                        StringValuePair temp = new StringValuePair(buff, changeCost, changeCost + this.LD(buff, target));
                        this.addToFronter(fronter, temp, explored);
                    }
                }
            }
            // anagram
            // if current string if anagram to the target
            int anagramCost = cost +  this.anagramCost();
            if(checkAnagram(cur, target)){
                StringValuePair temp = new StringValuePair(target, anagramCost, anagramCost);
                this.addToFronter(fronter, temp, explored);
            } 
            else {// get the anagram list from the current String
                List<String> anagramList = this.getAnagramList(cur);
                if(anagramList != null){
                    for(String anagram : anagramList){
                        if(!anagram.equals(cur)) {
                            if(this.checkValid(cur, target, anagramCost, explored)){
                                StringValuePair temp = new StringValuePair(cur, anagramCost, anagramCost + this.LD(anagram, target));
                                this.addToFronter(fronter, temp, explored);
                            }
                        }
                    }
                }
            }
        }

    }

    // helper method to validify the children string
    private boolean checkValid(String cur, String target, int cost, HashMap<String, Integer> explored){
        // case 1, check valid word
        if(!isWord(cur)) return false;
        // case 2 check lower bound and upper bound compared with current string length;
        if(cur.length() <= 3 || cur.length() > this.maxWordLen) return false;
        // case 3 if target has been found and current cost exceed target cost 
        if(explored.containsKey(target) && explored.get(target) < cost) return false; 
        return true;
    }
    // read instructions for given input file
    private void readInstruction(String filePath){
        try {
            Path path = Paths.get(filePath);
            List<String> lines = Files.readAllLines(path, Charset.defaultCharset());
            lines = new ArrayList(lines);

            if(lines.size() != 3) {
                throw new IllegalArgumentException("Invalid input");
            } 
            String[] costs = lines.get(0).trim().split(" ");
            if(costs.length != 4) {
                throw new IllegalArgumentException("Invalid input");
            } 
            for(int i = 0; i < costs.length; i++){
                operations[i] = Integer.parseInt(costs[i]);
            }
            this.origin = lines.get(1).trim().toLowerCase();
            this.target = lines.get(2).trim().toLowerCase();
        } 
        catch (IOException e) {
            System.out.println(e);
        }
    }

    private void loadDictionary(String wordFile)
    {
        try {
            Path path = Paths.get(wordFile);
            byte[] readBytes = Files.readAllBytes(path);
            String wordListContents = new String(readBytes, "UTF-8");
            String[] words = wordListContents.split("\n");
            for(String word:words){
                word = word.trim().toLowerCase();
                this.maxWordLen = Math.max(this.maxWordLen, word.length());
                wordsSet.add(word);
            }
        } catch(IOException e){
            System.out.println(e);
        }
    }


    // method that generate the anagram table using
    // the string formed by its sorted characters as the key
    private void creatAnagramTable(){
        for(String word: this.wordsSet){
            String key = mapToProduct(word);
            if(this.anagrams.containsKey(key)){
                this.anagrams.get(key).add(word);
            }
            else {
                List<String> temp = new ArrayList<String>();
                temp.add(word);
                this.anagrams.put(key, temp);
            }
        }
    }
    // mapping function which return sorted string
    private String mapToProduct(String word){
        char[] buf = word.toCharArray();
        Arrays.sort(buf);
        String result = new String(buf);
        return result;
    }

    private boolean isWord(String cur){
        return this.wordsSet.contains(cur);
    }

    private String add(int index, String cur, char insertValue){
        StringBuilder result = new StringBuilder(cur);
        return result.insert(index, insertValue).toString();
    }

    private String delete(int index, String cur){	
        StringBuilder result = new StringBuilder(cur);
        return result.deleteCharAt(index).toString();
    }

    private String change(String cur, int index, char changTo){
        StringBuilder result = new StringBuilder(cur);
        result.setCharAt(index, changTo);
        return result.toString();
    }
    
    // check if given two string are anagrams
    private boolean checkAnagram(String cur, String target){    
        Map<Character, Integer> chars = new HashMap();
        char[] temp = cur.toCharArray();
        for(char c: temp){
            if(chars.containsKey(c)) {
                chars.put(c, chars.get(c) + 1);
            }
            else chars.put(c, 1);
        }
        temp = target.toCharArray();
        for(char c: temp){
            if(chars.containsKey(c) && chars.get(c) >= 0) {
                chars.put(c, chars.get(c) - 1);
            }
            else return false;
        }
        return true;
    }

    private List<String> getAnagramList(String source){
        if(this.anagrams.containsKey(this.mapToProduct(source))){
            return anagrams.get(this.mapToProduct(source));
        }
        return null;
    }

    // dp algorithm for calculating the Levenshtein distance for given two strings
    private int LD (String s, String t) {
        int n = s.length ();
        int m = t.length ();
        // edge case 
        if (n == 0) return m;
        if (m == 0) return n;
        // declare dp matrix
        int[][] dp = new int[n+1][m+1];

        for (int i = 0; i <= n; i++) {
            dp[i][0] = i * this.deleteCost();
        }
        for (int j = 0; j <= m; j++) {
            dp[0][j] = j * this.addCost();
        }
        for (int i = 1; i <= n; i++) {
            char s_i = s.charAt (i - 1);
            for (int j = 1; j <= m; j++) {
                char t_j = t.charAt (j - 1);
                int cost = 0;
                if (s_i != t_j) cost = this.changeCost();
                dp[i][j] = Math.min(dp[i-1][j] + this.deleteCost(), 
                Math.min(dp[i][j-1] + this.addCost(), dp[i-1][j-1] + cost)); 
            }
        }
        return dp[n][m];
    }
    // add current source object into the fronter
    private void addToFronter(PriorityQueue<StringValuePair> fronter , StringValuePair source, 
    HashMap<String, Integer> explored){

        if(explored.containsKey(source.getStr())){
            if(explored.get(source.getStr()) <  source.getCost()) return;
        }
        for (Object element: fronter.toArray()) {
            StringValuePair cur = (StringValuePair)element;
            if(cur.getStr().equals(source.getStr())){
                if(cur.getHeur() > source.getHeur()){
                    fronter.remove(cur);
                    fronter.add(source);
                }
                return;
            }
        }
        fronter.add(source);
    }
    private String getStart(){
        return this.origin;
    }
    private String getTarget(){
        return this.target;
    }
    private int deleteCost(){
        return this.operations[1];
    }

    private int addCost(){
        return this.operations[0];
    }
    
    private int changeCost(){
        return this.operations[2];
    }
    
    private int anagramCost(){
        return this.operations[3];
    }
}