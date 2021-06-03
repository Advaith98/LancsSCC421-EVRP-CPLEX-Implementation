/*********************************************
 * OPL 20.1.0.0 Model
 * Author: D2
 * Creation Date: 10 May 2021 at 13:38:58
 *********************************************/
 
 //data parameters
int n = ...; //max number of customers; from data
int s = ...; //max number of chargepoints; from data
int m = ...; //max number of EVs dispatched; from data
range customerSetRange = 1..n;
range chargingStationSetRange =  1..s;
 

{int} customerSet = asSet(customerSetRange); // var N0 in definintion
{int} depot = {0}; // var O in definition
{int} depotChargingStation = {0};
{int} vertexSet = depot union customerSet; // var N in definition

{int} chargingStationSet = {n+i | i in chargingStationSetRange} union depotChargingStation; // var F in definition

{int} G = vertexSet union chargingStationSet; // var G in definition

range numberOfEVs = 1..m; // var M in definition

tuple vEdge{
  int i;
  int j;
  int m;
} // var ijm for defintion

tuple edge{
  int i;
  int j;
} // var ij for definition

setof (vEdge) vehicleEdges = {<i,j,m>| i,j in G, m in numberOfEVs : i!=j};
setof (edge) arc = {<i,j>| i,j in G :i!=j}; //var A in definition

tuple location{
  float x;
  float y;
} // for dummy location generation

location customerLocation[vertexSet];
location chargerStationLocation[chargingStationSet];

float travelTime[arc]; // var tij in definition
float distance[arc]; // var dij in definition
float travelSpeed[arc]; // var vij in definition
int demandedLoad[G] = ...; // var Di in definition 
int serviceType[G] = ...; // var ui in definition 
float handlingTime[G] = ...; //var hi in definition 
float driverHourlyWage = ...; // var Ctt in definition 
float batteryChargingMoneyRate = ...; // var Ce in definition 
int genericBatteryCapacity = ...;
int batteryCapacity[i in numberOfEVs] = genericBatteryCapacity; // var Cm in definition 
float genericVehicleCapacity = ...;
float vehicleCapacity[i in numberOfEVs] = genericVehicleCapacity; // var Qm in definition 
int rechargingRate = ...; // var r in defintion 
int workHourLimit = 8; // var H in defintion
int acceleration = ...; // var a in definition
float gravitationalConstant = ...; // var g in defintion 
int genericRoadAngle = ...;
int roadAngle[a in arc] = genericRoadAngle; // var theta in definition
//float energyConsumption[arc]; 
float rollingResistanceCoefficient = ...; // var Cr in definition 
float arcSpecficConstant[arc] ; // var alpha-ij in the definition 
float vehicleCurbWeight = ...; // var w in definition 
float engineEfficiency = ...; // var ef in definition 
float rollingDragCoefficient = ...; // var Cd in definition 
int frontalSurfaceArea = ...; // var A in definition 
float airDensity = ...; // var greekP in definition 
float vehicleSpecificConstant; // var beta in definition ... to be defined

//decision variables	
dvar boolean x[vehicleEdges]; //var xijm in definition
dvar float remainingBatteryCapacity[vehicleEdges]; //var yijm in definition
dvar float load[arc]; //var lij in definition
dvar float+ departureTime[arc]; // var tow-ij in defition

execute initializing{
  function getDistance(city1, city2){
     return Opl.sqrt(Opl.pow(city2.x - city1.x, 2) + Opl.pow(city2.y - city1.y, 2));
   }
   
  function getEnergyConsumption(arc , aSC){
    return ((aSC *(vehicleCurbWeight + load[arc])*distance[arc]) + (vehicleSpecificConstant * (Math.pow(travelSpeed[arc], 2))*distance[arc]))/engineEfficiency;
  } 
  
  for(var i in vertexSet ){
    if(i==0){
      customerLocation[i].x = 0;
      customerLocation[i].y = 0;
      continue;
    }
    customerLocation[i].x = Opl.rand(10);
    customerLocation[i].y = Opl.rand(10);
  }
  
  for(var i in chargingStationSet){
    if (i==0){
      chargerStationLocation[i].x = 0;
      chargerStationLocation[i].y = 0;
      continue;
    }
    chargerStationLocation[i].x = Opl.rand(10);
    chargerStationLocation[i].y = Opl.rand(10);
  }
  
  vehicleSpecificConstant = 0.5 * rollingDragCoefficient * frontalSurfaceArea * airDensity;
 
  for(var a in arc){
    arcSpecficConstant[a] = acceleration + (gravitationalConstant * Math.sin(roadAngle[a])) + (gravitationalConstant * rollingResistanceCoefficient * Math.cos(roadAngle[a]));
    travelSpeed[a]=10;
    if(chargingStationSet.contains(a.i) && chargingStationSet.contains(a.j)){
      distance[a] = getDistance(chargerStationLocation[a.i], chargerStationLocation[a.j]);
      travelTime[a] = distance[a]/travelSpeed[a];
      continue;
      }
    else if(chargingStationSet.contains(a.i) && customerSet.contains(a.j)){           
      distance[a] = getDistance(chargerStationLocation[a.i], customerLocation[a.j]);
      travelTime[a] = distance[a]/travelSpeed[a];
      continue;  
      }
    else if(customerSet.contains(a.i) && chargingStationSet.contains(a.j) ){
      distance[a] = getDistance(customerLocation[a.i], chargerStationLocation[a.j]);
      travelTime[a] = distance[a]/travelSpeed[a];
      continue;
      }
    else if(customerSet.contains(a.i) && customerSet.contains(a.j)){
      distance[a] = getDistance(customerLocation[a.i], customerLocation[a.j]);
      travelTime[a] = distance[a]/travelSpeed[a];
      continue;
      }
   }  
}

dexpr float energyConsumption[<i,j> in arc] = ((arcSpecficConstant[<i,j>] *(vehicleCurbWeight + load[<i,j>])*distance[<i,j>]) + (vehicleSpecificConstant * (travelSpeed[<i,j>]* travelSpeed[<i,j>]))*distance[<i,j>])/engineEfficiency;

dexpr float ZeX = (sum(<i,j> in arc :i!=j) sum (m in numberOfEVs) (batteryChargingMoneyRate * arcSpecficConstant[<i,j>] * vehicleCurbWeight * distance[<i,j>] * x[<i,j,m>]/engineEfficiency)) + (sum(<i,j> in arc :i!=j) sum (m in numberOfEVs) (batteryChargingMoneyRate * arcSpecficConstant[<i,j>] * load[<i,j>] * distance[<i,j>]/engineEfficiency)) + (sum(<i,j> in arc :i!=j) sum (m in numberOfEVs) (batteryChargingMoneyRate * vehicleSpecificConstant * travelSpeed[<i,j>] * travelSpeed[<i,j>] * distance[<i,j>] * x[<i,j,m>]/engineEfficiency));
dexpr float ZttX = sum(<i,j> in arc :i!=j) sum( m in numberOfEVs) driverHourlyWage * travelTime[<i,j>] * x[<i,j,m>];
dexpr float ZrX = sum(i in G, j in chargingStationSet : i!=j) sum(m in numberOfEVs) driverHourlyWage * ((batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate)*x[<i,j,m>];

dexpr float totalTravelEnergyCost = ZeX + ZttX + ZrX  ;

minimize totalTravelEnergyCost;
subject to{
  
  forall(m in numberOfEVs)
    mostEVsDispatchedRestriction:
    sum(j in vertexSet : j!=0) x[<0,j,m>]==1;
    
  forall(i in customerSet, m in numberOfEVs)
    eachCustomerVisitedOnce:
    sum(j in G : i!=j) x[<i,j,m>]==1;
    
  forall(j in G, m in numberOfEVs)
    flowConservation:
    sum(i in G :i!=j) x[<i,j,m>] == sum(k in G :k!=j) x[<j,k,m>];

    sum(m in numberOfEVs) sum(i in G) sum(j in customerSet : j!=i) x[<i,j,m>] == 1;
    sum(m in numberOfEVs) sum(j in G) sum(i in customerSet: i!=j) x[<i,j,m>] == 1;
    sum(m in numberOfEVs) sum(j in G : j!=0) x[<0,j,m>] == 1;
    sum(m in numberOfEVs) sum(j in customerSet : j!=0) x[<j,0,m>] == 1;
    
  forall(i in G)
    demandConservation:
    sum(j in G : i!=j) load[<j,i>] -
    sum(j in G : i!=j) load[<i,j>] 
    == 
    demandedLoad[i] * serviceType[i];
    
  forall(i,j in G, m in numberOfEVs :  i!=j){    
    demandAccomadationInVehicle:
    ((1 - serviceType[j] ) * demandedLoad[j] * serviceType[j]* x[<i,j,m>])/2 
    <=
    load[<i,j>] 
    && 
    load[<i,j>] 
    <= 
    (vehicleCapacity[m] * 
    x[<i,j,m>]) - 
    (((1 + serviceType[j]) * demandedLoad[j] * serviceType[j] * x[<i,j,m>])/2) ;
  }
    
  forall(i,j in G, m in numberOfEVs : i!=j){    
    loadWithinVehicleCapacity:
    0 
    <= 
    load[<i,j>] 
    &&
    load[<i,j>]
    <= 
    vehicleCapacity[m] - ((serviceType[i] - 1) * demandedLoad[i] * serviceType[i])/2;
  }
    
  forall(k,i in G, j in vertexSet, m in numberOfEVs : i!=j && j!=k && k!=i){    
    deliveryTimeManagment:
    workHourLimit*(x[<i,j,m>] - 1) 
    <= 
    departureTime[<k,i>] + 
    travelTime[<i,j>] + 
    handlingTime[j] - 
    departureTime[<i,j>] 
    &&
    departureTime[<k,i>] + 
    travelTime[<i,j>] + 
    handlingTime[j] - 
    departureTime[<i,j>] 
    <= 
    workHourLimit*(1- x[<i,j,m>]);
  }
    
  forall(k,i in G, j in chargingStationSet, m in numberOfEVs : i!=j && j!=k && k!=i){    
    chargingStationTimeManagement:
    workHourLimit*(x[<i,j,m>] - 1) 
    <=
    departureTime[<k,i>] + 
    travelTime[<i,j>] + 
    ((batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate) - departureTime[<i,j>] 
    && 
    departureTime[<k,i>] + 
    travelTime[<i,j>] + 
    ((batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate) - departureTime[<i,j>]
    <=  
    workHourLimit*(1- x[<i,j,m>] );
  }
    
  forall(i,j in G, m in numberOfEVs : i!=j){
    workHourLimitation:
    (x[<i,j,m>]==1) 
    => 
    ((sum(<i,j> in arc : i!=j) travelTime[<i,j>]* x[<i,j,m>]) 
    + 
    (sum(i in G, j in vertexSet : i!=j)handlingTime[j] * x[<i,j,m>]) 
    + 
    (sum(i in G, j in chargingStationSet :i!=j)((batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate)) 
    <= 
    workHourLimit);
    
    (x[<i,j,m>]==0) 
    => 
    (0
    <= 
    (batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate 
    &&
    (batteryCapacity[m] - remainingBatteryCapacity[<i,j,m>])/rechargingRate 
    <= 
    workHourLimit 
    * 
    (sum (i in G :i!=j) x[<i,j,m>]));
  } 
  
  forall(j in customerSet, m in numberOfEVs ){
    startBatteryCapacity:    
    remainingBatteryCapacity[<0,j,m>]== batteryCapacity[m];
  }   
    
  forall(i in chargingStationSet, j in vertexSet, m in numberOfEVs : i!=j){    
    batteryFullAtDepartureOfChargingStation:
    batteryCapacity[m]
    *
    (x[<i,j,m>] -1) 
    <= 
    remainingBatteryCapacity[<i,j,m>] - 
    (batteryCapacity[m] 
    - 
    energyConsumption[<i,j>]) 
    && 
    remainingBatteryCapacity[<i,j,m>] - 
    (batteryCapacity[m] 
    - 
    energyConsumption[<i,j>])
    <=
    batteryCapacity[m]
    *
    (1 - x[<i,j,m>]);
  }
    
  forall(i in customerSet, k,j in G, m in numberOfEVs : i!=j && j!=k && k!=i){    
    batteryCapacity[m]
    *
    (x[<i,j,m>] -1)
    <= 
    remainingBatteryCapacity[<i,j,m>] - 
    (remainingBatteryCapacity[<k,i,m>] - 
    energyConsumption[<i,j>]) 
    && 
    remainingBatteryCapacity[<i,j,m>] - 
    (remainingBatteryCapacity[<k,i,m>] - 
    energyConsumption[<i,j>]) 
    <= 
    batteryCapacity[m]
    *
    (1 - x[<i,j,m>]);
  }
    
  forall(i,j in G, m in numberOfEVs : i!=j){
    remainingBatteryWithinCapacity:
    0
    <=
    remainingBatteryCapacity[<i,j,m>]
    &&
    remainingBatteryCapacity[<i,j,m>] 
    <=
    batteryCapacity[m];
  }
    
  forall(j in G : j!=0)
    startTimeInitialization:
    departureTime[<0,j>] == 0;
    
  forall(i,j in G : i!=j)
    distanceTimeSpeedRelationship:
    distance[<i,j>] == travelSpeed[<i,j>] * travelTime[<i,j>]; 
}