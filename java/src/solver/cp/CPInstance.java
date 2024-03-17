package solver.cp;

import ilog.cp.*;

import ilog.concert.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class CPInstance
{
  // BUSINESS parameters
  int numWeeks;
  int numDays;  
  int numEmployees;
  int numShifts;
  int numIntervalsInDay;
  int[][] minDemandDayShift;
  int minDailyOperation;
  
  // EMPLOYEE parameters
  int minConsecutiveWork;
  int maxDailyWork;
  int minWeeklyWork;
  int maxWeeklyWork;
  int maxConsecutiveNightShift;
  int maxTotalNightShift;

  // ILOG CP Solver
  IloCP cp;

  //My variable
  int[][] beginED;
  int[][] endED;
    
  public CPInstance(String fileName)
  {
    try
    {
      Scanner read = new Scanner(new File(fileName));
      
      while (read.hasNextLine())
      {
        String line = read.nextLine();
        String[] values = line.split(" ");
        if(values[0].equals("Business_numWeeks:"))
        {
          numWeeks = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numDays:"))
        {
          numDays = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numEmployees:"))
        {
          numEmployees = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numShifts:"))
        {
          numShifts = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_numIntervalsInDay:"))
        {
          numIntervalsInDay = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Business_minDemandDayShift:"))
        {
          int index = 1;
          minDemandDayShift = new int[numDays][numShifts];
          for(int d=0; d<numDays; d++)
            for(int s=0; s<numShifts; s++)
              minDemandDayShift[d][s] = Integer.parseInt(values[index++]);
        }
        else if(values[0].equals("Business_minDailyOperation:"))
        {
          minDailyOperation = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_minConsecutiveWork:"))
        {
          minConsecutiveWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxDailyWork:"))
        {
          maxDailyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_minWeeklyWork:"))
        {
          minWeeklyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxWeeklyWork:"))
        {
          maxWeeklyWork = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxConsecutiveNigthShift:"))
        {
          maxConsecutiveNightShift = Integer.parseInt(values[1]);
        }
        else if(values[0].equals("Employee_maxTotalNigthShift:"))
        {
          maxTotalNightShift = Integer.parseInt(values[1]);
        }
      }
    }
    catch (FileNotFoundException e)
    {
      System.out.println("Error: file not found " + fileName);
    }
  }

  IloIntVar[] flatten(IloIntVar[][] x){
    IloIntVar[] x_flat = new IloIntVar[x[0].length * x.length];
    int index = 0;
    for(int i = 0; i < x.length; i++){
      for(int j = 0; j < x[0].length; j++){
        x_flat[index] = x[i][j];
        index += 1;
      }
    }
    return x_flat;
  }

  public void solve()
  {
    try
    {
      cp = new IloCP();
      // TODO: Employee Scheduling Model Goes Here
      //creating the variable for the shift matrix and assigning its domain
      int[] shiftDomainValues = {0, 1, 2, 3};
      IloIntVar[][] shiftEmployeeDay = new IloIntVar[numEmployees][numDays];
      for(int i = 0; i < numEmployees; i++){
        for(int j = 0; j < numDays; j++){
          shiftEmployeeDay[i][j] = cp.intVar(shiftDomainValues); 
        }
      }

      //creating the variable for hours matrix and assigning its domain
      int[] durationDomainValues = {0, 4, 5, 6, 7, 8};
      IloIntVar[][] durationEmployeeDay = new IloIntVar[numEmployees][numDays];
      for(int i = 0; i < numEmployees; i++){
        for(int j = 0; j < numDays; j++){
          durationEmployeeDay[i][j] = cp.intVar(durationDomainValues);
        }
      }

      //constraint 1 - shift i,j is not off equivalent to duration i,j not 0
      for(int i = 0; i < numEmployees; i++){
        for(int j = 0; j < numDays; j++){
          cp.add(cp.ifThen(cp.neq(durationEmployeeDay[i][j], 0), cp.neq(shiftEmployeeDay[i][j], 0)));
          cp.add(cp.ifThen(cp.neq(shiftEmployeeDay[i][j], 0), cp.neq(durationEmployeeDay[i][j], 0)));
        }
      }

      //constraint 2 - cannot work consecutive night shifts

    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays - 1; j++){
        cp.add(cp.ifThen(cp.eq(shiftEmployeeDay[i][j], 1), cp.neq(shiftEmployeeDay[i][j + 1], 1)));
      }
    }

    //constraint 3 - Weekly working constraint
    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays; j+=7){
        IloIntVar[] weeklyHours = new IloIntVar[7];
        weeklyHours[0] = durationEmployeeDay[i][j];
        weeklyHours[1] = durationEmployeeDay[i][j + 1];
        weeklyHours[2] = durationEmployeeDay[i][j + 2];
        weeklyHours[3] = durationEmployeeDay[i][j + 3];
        weeklyHours[4] = durationEmployeeDay[i][j + 4];
        weeklyHours[5] = durationEmployeeDay[i][j + 5];
        weeklyHours[6] = durationEmployeeDay[i][j + 6];
        cp.add(cp.le(cp.sum(weeklyHours), maxWeeklyWork));
        cp.add(cp.ge(cp.sum(weeklyHours), minWeeklyWork));
      }
    }

    //constraint 4 - Max night shift constraint
    for(int i = 0; i < numEmployees; i++){
      cp.add(cp.le(cp.count(shiftEmployeeDay[i], 1), maxTotalNightShift));
    }

    //constraint 5 - First 4 days all diff constraint
    for(int i = 0; i < numEmployees; i++){
      IloIntVar[] trainingDays = new IloIntVar[4];
      trainingDays[0] = shiftEmployeeDay[i][0];
      trainingDays[1] = shiftEmployeeDay[i][1];
      trainingDays[2] = shiftEmployeeDay[i][2];
      trainingDays[3] = shiftEmployeeDay[i][3];
      cp.add(cp.allDiff(trainingDays));
    }

    //constraint 6 - min number of employees per shift per day
    for(int j = 0; j < numDays; j++){
      IloIntVar[] shiftsOnDay = new IloIntVar[numEmployees];
      for(int i = 0; i < numEmployees; i++){
        shiftsOnDay[i] = shiftEmployeeDay[i][j];
      }
      cp.add(cp.ge(cp.count(shiftsOnDay, 0), minDemandDayShift[j][0]));
      cp.add(cp.ge(cp.count(shiftsOnDay, 1), minDemandDayShift[j][1]));
      cp.add(cp.ge(cp.count(shiftsOnDay, 2), minDemandDayShift[j][2]));
      cp.add(cp.ge(cp.count(shiftsOnDay, 3), minDemandDayShift[j][3]));
    }

    //constraint 7 - min daily operation
    for(int j = 0; j < numDays; j++){
      IloIntVar[] durationOnDay = new IloIntVar[numEmployees];
      for(int i = 0; i < numEmployees; i++){
        durationOnDay[i] = durationEmployeeDay[i][j];
      }
      cp.add(cp.ge(cp.sum(durationOnDay), minDailyOperation));
    }


        
      // Important: Do not change! Keep these parameters as is
      cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
      cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);  
      IloVarSelector[] vs = new IloVarSelector[2];
      vs[0] = cp.selectSmallest(cp.domainSize());
      vs[1] = cp.selectRandomVar();
      IloValueSelector minSelect = cp.selectSmallest(cp.value());
      IloValueSelector maxSelect = cp.selectLargest(cp.value());
      IloIntValueChooser minChooser = cp.intValueChooser(minSelect);
      IloIntValueChooser maxChooser = cp.intValueChooser(maxSelect);
      IloIntVarChooser varChooser = cp.intVarChooser(vs);
      IloSearchPhase[] phases = new IloSearchPhase[2 * numDays];
      for(int j = 0; j < numDays; j++){
        IloIntVar[] shiftsDay = new IloIntVar[numEmployees];
        IloIntVar[] durationDay = new IloIntVar[numEmployees];
        for(int i = 0; i < numEmployees; i++){
          shiftsDay[i] = shiftEmployeeDay[i][j];
          durationDay[i] = durationEmployeeDay[i][j];
        }
        phases[2 * j] = cp.searchPhase(shiftsDay, varChooser, maxChooser);
        phases[(2 * j) + 1] = cp.searchPhase(durationDay, varChooser, minChooser);
      }
      cp.setSearchPhases(phases);

      // IloVarSelector varSelector1 = cp.selectSmallest(cp.domainSize());
      // int[] weights = {0, 100, -1, -1, -1, 20};
      // IloIntValueEval valEval = cp.explicitValueEval(durationDomainValues, weights);
      // IloValueSelector valSelectorDuration = cp.selectLargest(valEval);
      // IloValueSelector valSelectorShifts = cp.selectRandomValue();
      // IloIntVar[][] trainingShifts = new IloIntVar[numEmployees][4];
      // IloIntVar[][] trainingDuration = new IloIntVar[numEmployees][4];
      // IloIntVar[][] remainingShifts = new IloIntVar[numEmployees][numDays - 4];
      // IloIntVar[][] remainingDuration = new IloIntVar[numEmployees][numDays - 4];
      // for(int i = 0; i < numEmployees; i++){
      //   for(int j = 0; j < 4; j++){
      //     trainingShifts[i][j] = shiftEmployeeDay[i][j];
      //     trainingDuration[i][j] = durationEmployeeDay[i][j];
      //   }
      // }
      // for(int i = 0; i < numEmployees; i++){
      //   for(int j = 4; j < numDays; j++){
      //     remainingShifts[i][j - 4] = shiftEmployeeDay[i][j];
      //     remainingDuration[i][j - 4] = durationEmployeeDay[i][j];
      //   }
      // }
      // IloSearchPhase[] phases = new IloSearchPhase[4];
      // phases[0] = cp.searchPhase(flatten(trainingShifts), cp.intVarChooser(varSelector1), cp.intValueChooser(valSelectorShifts));
      // phases[1] = cp.searchPhase(flatten(trainingDuration), cp.intVarChooser(varSelector1), cp.intValueChooser(valSelectorDuration));
      // phases[2] = cp.searchPhase(flatten(remainingShifts), cp.intVarChooser(varSelector1), cp.intValueChooser(valSelectorShifts));
      // phases[3] = cp.searchPhase(flatten(remainingDuration), cp.intVarChooser(varSelector1), cp.intValueChooser(valSelectorDuration));
      // cp.setSearchPhases(phases);
      // IloValueSelector valSelector1 = cp.selectSmallest(cp.value());
      // IloValueSelector valSelector2 = cp.selectLargest(cp.value())
      // IloIntVarChooser varChooser = cp.intVarChooser(varSelector);
      // IloIntValueChooser valChooser = cp.intValueChooser(valSel);
      // IloSearchPhase shiftsSearch = cp.searchPhase(flatten(shiftEmployeeDay), varChooser, valChooser);
      // IloSearchPhase durationSearch = cp.searchPhase(flatten(durationEmployeeDay), varChooser, valChooser);
      // IloSearchPhase[] phases = new IloSearchPhase[2];
      // phases[0] = shiftsSearch;
      // phases[1] = durationSearch;
      // cp.setSearchPhases(phases);
      // Uncomment this: to set the solver output level if you wish
      // cp.setParameter(IloCP.IntParam.LogVerbosity, IloCP.ParameterValues.Quiet);
      if(cp.solve())
      {
        cp.printInformation();

        int[] shiftHours = {-1, 0, 8, 16};
        beginED = new int[numEmployees][numDays];
        endED = new int[numEmployees][numDays];
        for(int i = 0; i < numEmployees; i++){
          for(int j = 0; j < numDays; j++){
            beginED[i][j] = shiftHours[(int)cp.getValue(shiftEmployeeDay[i][j])];
            endED[i][j] = shiftHours[(int)cp.getValue(shiftEmployeeDay[i][j])] + (int)cp.getValue(durationEmployeeDay[i][j]);
          }
        }
        
        // Uncomment this: for poor man's Gantt Chart to display schedules
        prettyPrint(numEmployees, numDays, beginED, endED);	
      }
      else
      {
        System.out.println("No Solution found!");
        System.out.println("Number of fails: " + cp.getInfo(IloCP.IntInfo.NumberOfFails));
      }
    }
    catch(IloException e)
    {
      System.out.println("Error: " + e);
    }
  }


  String printSolution(){
    String output = "";
    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays; j++){
        if(i == 0 && j == 0){
          output += Integer.toString(beginED[i][j]) + " " + Integer.toString(endED[i][j]);
        }
        else{
          output += " " + Integer.toString(beginED[i][j]) + " " + Integer.toString(endED[i][j]);
        }
      }
    }
    return output;
  }

  void checkConst1(){
    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays; j++){
        if(beginED[i][j] == -1){
          if(endED[i][j] != -1){
            System.out.println("CONSTRAINT1 is UNSAT");
            return;
          }
        }
      }
    }
    System.out.println("CONSTRAINT1 is SAT");
  }

  void checkConst2(){
    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays - 1; j++){
        if(beginED[i][j] == 0){
          if(beginED[i][j + 1] == 0){
            System.out.println("CONSTRAINT2 is UNSAT");
            return;
          }
        }
      }
    }
    System.out.println("CONSTRAINT2 is SAT");
  }

  void checkConst3(){
    for(int i = 0; i < numEmployees; i++){
      for(int j = 0; j < numDays; j+=7){
        int workInWeek = 0;
        workInWeek += endED[i][j] - beginED[i][j];
        workInWeek += endED[i][j + 1] - beginED[i][j + 1];
        workInWeek += endED[i][j + 2] - beginED[i][j + 2];
        workInWeek += endED[i][j + 3] - beginED[i][j + 3];
        workInWeek += endED[i][j + 4] - beginED[i][j + 4];
        workInWeek += endED[i][j + 5] - beginED[i][j + 5];
        workInWeek += endED[i][j + 6] - beginED[i][j + 6];
        System.out.println(workInWeek);
        if(workInWeek > maxWeeklyWork || workInWeek < minWeeklyWork){
          System.out.println("CONSTRAIN3 is UNSAT");
          return;
        }
      }
    }
    System.out.println("CONSTRAINT3 is SAT");
  }

  void checkConst4(){
    for(int i = 0; i < numEmployees; i++){
      int nightShifts = 0;
      for(int j = 0; j < numDays; j++){
        if(beginED[i][j] == 0){
          nightShifts += 1;
        }
      }
      if(nightShifts > maxTotalNightShift){
        System.out.println("CONSTRAIN 4 is UNSAT");
        return;
      }
    }
    System.out.println("CONSTRAINT4 is SAT");
  }

  void checkConst5(){
    for(int i = 0; i < numEmployees; i++){
      HashSet<Integer> allDif = new HashSet<Integer>();
      allDif.add(0);
      allDif.add(-1);
      allDif.add(8);
      allDif.add(16);
      for(int j = 0; j < 4; j++){
        allDif.remove(beginED[i][j]);
      }
      if(!allDif.isEmpty()){
        System.out.println("CONSTRAINT5 is UNSAT");
        return;
      }
    }
    System.out.println("CONSTRAINT5 is SAT");
  }

  void checkConst6(){
    for(int j = 0; j < numDays; j++){
      int off = 0;
      int night = 0;
      int day = 0;
      int evening = 0;
      for(int i = 0; i < numEmployees; i++){
        if(beginED[i][j] == -1){
          off += 1;
        }
        else if(beginED[i][j] == 0){
          night += 1;
        }
        else if(beginED[i][j] == 8){
          day += 1;
        }
        else{
          evening += 1;
        }
      }
      if(off < minDemandDayShift[j][0]){
        System.out.println("CONSTRAIN 6 is UNSAT");
        return;
      }
      if(night < minDemandDayShift[j][1]){
        System.out.println("CONSTRAIN 6 is UNSAT");
        return;
      }
      if(day < minDemandDayShift[j][2]){
        System.out.println("CONSTRAIN 6 is UNSAT");
        return;
      }
      if(evening < minDemandDayShift[j][3]){
        System.out.println("CONSTRAIN 6 is UNSAT");
        return;
      }
    }
    System.out.println("CONSTRAINT 6 is SAT");
  }

  void checkConst7(){
    for(int j = 0; j < numDays; j++){
      int totalHours = 0;
      for(int i = 0; i < numEmployees; i++){
        totalHours += endED[i][j] - beginED[i][j];
      }
      if(totalHours < minDailyOperation){
        System.out.println("CONSTRAIN7 is UNSAT");
        return;
      }
    }
    System.out.println("CONSTRAINT 7 is SAT");
  }

  // SK: technically speaking, the model with the global constaints
  // should result in fewer number of fails. In this case, the problem 
  // is so simple that, the solver is able to re-transform the model 
  // and replace inequalities with the global all different constrains.
  // Therefore, the results don't really differ
  void solveAustraliaGlobal()
  {
    String[] Colors = {"red", "green", "blue"};
    try 
    {
      cp = new IloCP();
      IloIntVar WesternAustralia = cp.intVar(0, 3);
      IloIntVar NorthernTerritory = cp.intVar(0, 3);
      IloIntVar SouthAustralia = cp.intVar(0, 3);
      IloIntVar Queensland = cp.intVar(0, 3);
      IloIntVar NewSouthWales = cp.intVar(0, 3);
      IloIntVar Victoria = cp.intVar(0, 3);
      
      IloIntExpr[] clique1 = new IloIntExpr[3];
      clique1[0] = WesternAustralia;
      clique1[1] = NorthernTerritory;
      clique1[2] = SouthAustralia;
      
      IloIntExpr[] clique2 = new IloIntExpr[3];
      clique2[0] = Queensland;
      clique2[1] = NorthernTerritory;
      clique2[2] = SouthAustralia;
      
      IloIntExpr[] clique3 = new IloIntExpr[3];
      clique3[0] = Queensland;
      clique3[1] = NewSouthWales;
      clique3[2] = SouthAustralia;
      
      IloIntExpr[] clique4 = new IloIntExpr[3];
      clique4[0] = Queensland;
      clique4[1] = Victoria;
      clique4[2] = SouthAustralia;
      
      cp.add(cp.allDiff(clique1));
      cp.add(cp.allDiff(clique2));
      cp.add(cp.allDiff(clique3));
      cp.add(cp.allDiff(clique4));
      
	  cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
	  cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);   
	  
      if (cp.solve())
      {    
         System.out.println();
         System.out.println( "WesternAustralia:    " + Colors[(int)cp.getValue(WesternAustralia)]);
         System.out.println( "NorthernTerritory:   " + Colors[(int)cp.getValue(NorthernTerritory)]);
         System.out.println( "SouthAustralia:      " + Colors[(int)cp.getValue(SouthAustralia)]);
         System.out.println( "Queensland:          " + Colors[(int)cp.getValue(Queensland)]);
         System.out.println( "NewSouthWales:       " + Colors[(int)cp.getValue(NewSouthWales)]);
         System.out.println( "Victoria:            " + Colors[(int)cp.getValue(Victoria)]);
      }
      else
      {
        System.out.println("No Solution found!");
      }
    } catch (IloException e) 
    {
      System.out.println("Error: " + e);
    }
  }

  
  void solveAustraliaBinary()
  {
    String[] Colors = {"red", "green", "blue"};
    try 
    {
      cp = new IloCP();
      IloIntVar WesternAustralia = cp.intVar(0, 3);
      IloIntVar NorthernTerritory = cp.intVar(0, 3);
      IloIntVar SouthAustralia = cp.intVar(0, 3);
      IloIntVar Queensland = cp.intVar(0, 3);
      IloIntVar NewSouthWales = cp.intVar(0, 3);
      IloIntVar Victoria = cp.intVar(0, 3);
      
      cp.add(cp.neq(WesternAustralia , NorthernTerritory)); 
      cp.add(cp.neq(WesternAustralia , SouthAustralia)); 
      cp.add(cp.neq(NorthernTerritory , SouthAustralia));
      cp.add(cp.neq(NorthernTerritory , Queensland));
      cp.add(cp.neq(SouthAustralia , Queensland)); 
      cp.add(cp.neq(SouthAustralia , NewSouthWales)); 
      cp.add(cp.neq(SouthAustralia , Victoria)); 
      cp.add(cp.neq(Queensland , NewSouthWales));
      cp.add(cp.neq(NewSouthWales , Victoria)); 
      
	  cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
	  cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);   
	  
      if (cp.solve())
      {    
         System.out.println();
         System.out.println( "WesternAustralia:    " + Colors[(int)cp.getValue(WesternAustralia)]);
         System.out.println( "NorthernTerritory:   " + Colors[(int)cp.getValue(NorthernTerritory)]);
         System.out.println( "SouthAustralia:      " + Colors[(int)cp.getValue(SouthAustralia)]);
         System.out.println( "Queensland:          " + Colors[(int)cp.getValue(Queensland)]);
         System.out.println( "NewSouthWales:       " + Colors[(int)cp.getValue(NewSouthWales)]);
         System.out.println( "Victoria:            " + Colors[(int)cp.getValue(Victoria)]);
      }
      else
      {
        System.out.println("No Solution found!");
      }
    } catch (IloException e) 
    {
      System.out.println("Error: " + e);
    }
  }
  void solveAustraliaBinaryArray()
  {
    String[] Colors = {"red", "green", "blue"};
    try 
    {
      cp = new IloCP();
      IloIntVar WesternAustralia = cp.intVar(0, 3);
      IloIntVar NorthernTerritory = cp.intVar(0, 3);
      IloIntVar SouthAustralia = cp.intVar(0, 3);
      IloIntVar Queensland = cp.intVar(0, 3);
      IloIntVar NewSouthWales = cp.intVar(0, 3);
      IloIntVar Victoria = cp.intVar(0, 3);
      IloIntVar[] arr = cp.intVarArray(3) ; 
      for (int i = 0; i < arr.length; i++) {
        arr[i] = cp.intVar(3,5);
      }
      
      cp.add(cp.allDiff(arr)) ; 
      cp.add(cp.neq(WesternAustralia , NorthernTerritory)); 
      cp.add(cp.neq(WesternAustralia , SouthAustralia)); 
      cp.add(cp.neq(NorthernTerritory , SouthAustralia));
      cp.add(cp.neq(NorthernTerritory , Queensland));
      cp.add(cp.neq(SouthAustralia , Queensland)); 
      cp.add(cp.neq(SouthAustralia , NewSouthWales)); 
      cp.add(cp.neq(SouthAustralia , Victoria)); 
      cp.add(cp.neq(Queensland , NewSouthWales));
      cp.add(cp.neq(NewSouthWales , Victoria)); 
      
	  cp.setParameter(IloCP.IntParam.Workers, 1);
    cp.setParameter(IloCP.DoubleParam.TimeLimit, 300);
	  cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);   
	  
      if (cp.solve())
      {    
         System.out.println();
         System.out.println( "WesternAustralia:    " + Colors[(int)cp.getValue(WesternAustralia)]);
         System.out.println( "NorthernTerritory:   " + Colors[(int)cp.getValue(NorthernTerritory)]);
         System.out.println( "SouthAustralia:      " + Colors[(int)cp.getValue(SouthAustralia)]);
         System.out.println( "Queensland:          " + Colors[(int)cp.getValue(Queensland)]);
         System.out.println( "NewSouthWales:       " + Colors[(int)cp.getValue(NewSouthWales)]);
         System.out.println( "Victoria:            " + Colors[(int)cp.getValue(Victoria)]);
         for (IloIntVar x : arr) {
          System.out.println("arr val is : " + cp.getValue(x)) ;
         }
      }
      else
      {
        System.out.println("No Solution found!");
      }
    } catch (IloException e) 
    {
      System.out.println("Error: " + e);
    }
  }

  void solveSendMoreMoney()
  {
    try 
    {
      // CP Solver
      cp = new IloCP();
	
      // SEND MORE MONEY
      IloIntVar S = cp.intVar(1, 9);
      IloIntVar E = cp.intVar(0, 9);
      IloIntVar N = cp.intVar(0, 9);
      IloIntVar D = cp.intVar(0, 9);
      IloIntVar M = cp.intVar(1, 9);
      IloIntVar O = cp.intVar(0, 9);
      IloIntVar R = cp.intVar(0, 9);
      IloIntVar Y = cp.intVar(0, 9);
      
      IloIntVar[] vars = new IloIntVar[]{S, E, N, D, M, O, R, Y};
      cp.add(cp.allDiff(vars));
      
      //                1000 * S + 100 * E + 10 * N + D 
      //              + 1000 * M + 100 * O + 10 * R + E
      //  = 10000 * M + 1000 * O + 100 * N + 10 * E + Y 
      
      IloIntExpr SEND = cp.sum(cp.prod(1000, S), cp.sum(cp.prod(100, E), cp.sum(cp.prod(10, N), D)));
      IloIntExpr MORE   = cp.sum(cp.prod(1000, M), cp.sum(cp.prod(100, O), cp.sum(cp.prod(10,R), E)));
      IloIntExpr MONEY  = cp.sum(cp.prod(10000, M), cp.sum(cp.prod(1000, O), cp.sum(cp.prod(100, N), cp.sum(cp.prod(10,E), Y))));
      
      cp.add(cp.eq(MONEY, cp.sum(SEND, MORE)));
      
      // Solver parameters
      cp.setParameter(IloCP.IntParam.Workers, 1);
      cp.setParameter(IloCP.IntParam.SearchType, IloCP.ParameterValues.DepthFirst);
      if(cp.solve())
      {
        System.out.println("  " + cp.getValue(S) + " " + cp.getValue(E) + " " + cp.getValue(N) + " " + cp.getValue(D));
        System.out.println("  " + cp.getValue(M) + " " + cp.getValue(O) + " " + cp.getValue(R) + " " + cp.getValue(E));
        System.out.println(cp.getValue(M) + " " + cp.getValue(O) + " " + cp.getValue(N) + " " + cp.getValue(E) + " " + cp.getValue(Y));
      }
      else
      {
        System.out.println("No Solution!");
      }
    } catch (IloException e) 
    {
      System.out.println("Error: " + e);
    }
  }
  
 /**
   * Poor man's Gantt chart.
   * author: skadiogl
   *
   * Displays the employee schedules on the command line. 
   * Each row corresponds to a single employee. 
   * A "+" refers to a working hour and "." means no work
   * The shifts are separated with a "|"
   * The days are separated with "||"
   * 
   * This might help you analyze your solutions. 
   * 
   * @param numEmployees the number of employees
   * @param numDays the number of days
   * @param beginED int[e][d] the hour employee e begins work on day d, -1 if not working
   * @param endED   int[e][d] the hour employee e ends work on day d, -1 if not working
   */
  void prettyPrint(int numEmployees, int numDays, int[][] beginED, int[][] endED)
  {
    for (int e = 0; e < numEmployees; e++)
    {
      System.out.print("E"+(e+1)+": ");
      if(e < 9) System.out.print(" ");
      for (int d = 0; d < numDays; d++)
      {
        for(int i=0; i < numIntervalsInDay; i++)
        {
          if(i%8==0)System.out.print("|");
          if (beginED[e][d] != endED[e][d] && i >= beginED[e][d] && i < endED[e][d]) System.out.print("+");
          else  System.out.print(".");
        }
        System.out.print("|");
      }
      System.out.println(" ");
    }
  }

  /**
   * Generate Visualizer Input
   * author: lmayo1
   *
   * Generates an input solution file for the visualizer. 
   * The file name is numDays_numEmployees_sol.txt
   * The file will be overwritten if it already exists.
   * 
   * @param numEmployees the number of employees
   * @param numDays the number of days
   * @param beginED int[e][d] the hour employee e begins work on day d, -1 if not working
   * @param endED   int[e][d] the hour employee e ends work on day d, -1 if not working
   */
   void generateVisualizerInput(int numEmployees, int numDays, int[][] beginED, int[][] endED){
    String solString = String.format("%d %d %n", numDays,numEmployees);

    for (int d = 0; d <  numDays; d ++){
      for(int e = 0; e < numEmployees; e ++){
            solString += String.format("%d %d %n", (int)beginED[e][d], (int)endED[e][d]);
      }
    }

    String fileName = Integer.toString(numDays) + "_" + Integer.toString(numEmployees) + "_sol.txt";

    try {
      File resultsFile = new File(fileName);
      if (resultsFile.createNewFile()) {
        System.out.println("File created: " + fileName);
      } else {
        System.out.println("Overwritting the existing " + fileName);
      }
      FileWriter writer = new FileWriter(resultsFile, false);
      writer.write(solString);
      writer.close();
    } catch (IOException e) {
      System.out.println("An error occurred.");
      e.printStackTrace();
    }
}

}
