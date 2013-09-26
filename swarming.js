/****************************************************************
 ****************************************************************
 ** JS-Swarming!
 **
 ** A very simple implementation of swarming behavior in pure
 ** Javascript and SVG.
 **
 ** Features:
 ** - Basic biods.
 ** - Attractive/repulsive "emitters".
 ** - Predators!
 ** - Some real-time user interaction.
 **
 **
 ** Written by: Stephen Smithbower [smithy.s@gmail.com]
 ** Written on: September 25th, 2013.
 **
 ** Use as you wish!
 **
 **
 ** CONTROLS:
 ** --------------------------------------------------------------
 ** r		Resets the simulation
 ** k 		Adds an attractive emitter of a random size and strength at the current mouse position.
 **	l 		Adds a repulsive emitter of a random size and strength at the current mouse position.
 ** p 		Adds a new predator at a random position.
 ** b 		Adds a new biod at the current mouse position.
 **
 ** Left Mouse Down 			Pull the biods towards the mouse cursor.
 ** Left Mouse Down + Shift 	Push the biods away from the mouse cursor.			
 **
 *****************************************************************
 *****************************************************************/

//////////////////////////////////////////
// GLOBAL VARIABLES						//
//////////////////////////////////////////
var g_simulationInterval = null;
var t_delta = null;
var t_lastFrame = 0;

var g_flock = null;

var g_mouseEmitter = null;
var g_mouseIsDown = false;

var g_keysDown = {}; //Stores all current keypresses.

var g_pIsPressed = false;
var g_kIsPressed = false;
var g_lIsPressed = false;
var g_bIsPressed = false;
var g_rIsPressed = false;

var g_svg = null;

var g_mouseVec = new Vector(0,0);

//////////////////////////////////////////
// VECTOR CLASS							//
//////////////////////////////////////////
/**
 * Represents a basic 2D vector, as well as provides some
 * basic math convienance functions.
 */
function Vector(x, y)
{
	this.x = x;
	this.y = y;

	this.radsToDegs = 57.2957795;
	this.degsToRads = 0.0174532925;
}

Vector.prototype.clone = function() { return new Vector(this.x, this.y); };
Vector.prototype.toAngle = function()
	{
		var angle = Math.atan2(this.y, this.x);
		return angle < 0 ? angle + 2 * Math.PI : angle;
	}
Vector.prototype.toDegrees = function()
	{
		return this.toAngle() * this.radsToDegs;
	}
Vector.prototype.length = function()
	{
		return Math.sqrt(this.x * this.x + this.y * this.y);
	}
Vector.prototype.normalize = function()
	{
		var len = this.length();
		return len != 0 ? new Vector(this.x / len, this.y / len) : this;
	}
Vector.prototype.fromAngle = function(radians)
	{
		this.x = Math.cos(radians);
		this.y = Math.sin(radians);
	}
Vector.prototype.fromDegrees = function(degrees)
	{
		this.fromAngle(degrees * this.degsToRads);
	}
Vector.prototype.scale = function(amount)
	{
		return new Vector(this.x * amount, this.y * amount);
	}
Vector.prototype.getDistance = function(point)
	{
		return Math.sqrt(Math.pow(point.x - this.x, 2) + Math.pow(point.y - this.y, 2));
	}
Vector.prototype.getDirectionTo = function(point)
	{	
		return new Vector(point.x - this.x, point.y - this.y).normalize();
	}

Vector.prototype.add = function(amount)
	{
		return new Vector (this.x + amount.x, this.y + amount.y);
	}
Vector.prototype.dot = function(vector)
{
	return this.x * vector.x + this.y + vector.y;
}

Vector.prototype.inplaceAdd = function(amount)
	{
		this.x += amount.x;
		this.y += amount.y;
	}
Vector.prototype.getClosestPointOnLine = function(start, end)
	{
		var delta = new Vector(end.x - start.x, end.y - start.y);

		if (delta.x == 0 && delta.y == 0)
		{
			return start;
		}
		else
		{
			var dist = ((this.x - start.x) * delta.x + (this.y - start.y) * delta.y) / (delta.x * delta.x + delta.y * delta.y);
			dist = Math.min(Math.max(0, dist), 1);

			return new Vector(start.x + dist * delta.x, start.y + dist * delta.y);
		}

	}


//////////////////////////////////////////
// BIOD CLASS							//
//////////////////////////////////////////
/**
 * A biod is a little individual swarming entity. Biods follow the following three rules:
 * 
 * 1) Move in the same general direction as the group.
 * 2) Move towards the center of the group.
 * 3) Don't get too close to other individuals.
 *
 * We have some additional features. We support emitters, which emit either an attractive
 * or repulsive force (i.e. moths to a flame). Predators work by creating a moving repulsive
 * emitter.
 *
 * We also limit turning speed (biods must turn towards their new headings), this makes movement
 * much more natural and creates nice sweeping arcs.
 *
 * Our biods also have a limit on neighbors - they have a sight radius, which determines how far
 * around them they can see, and we use the dot product in order to ensure that we only "see"
 * neighbors that are in front of us (though we have 180 degree vision, haha).
 */
function Biod(position, speed, turnSpeed, radius, proximityRadius, sightRadius, claustrophobicSeverity, sandboxDimensions)
{
	this.position = position;
	this.speed = speed; //How fast we can zip about.
	this.turnSpeed = turnSpeed; //How fast we can turn towards new headings.
	this.radius = radius; //Our size.
	this.proximityRadius = proximityRadius; //How close is too close?
	this.sightRadius = sightRadius;
	this.claustrophobicSeverity = claustrophobicSeverity; //How strongly we dislike being close to others.
	this.sandboxDimensions = sandboxDimensions;

	this.majorInfluence = null; //Tracks which force is dominating our heading, for diagnostics.
	this.majorInfluenceStrength = null;

	this.emitterInfluences = new Array(); //A list of various influences affecting us.

	this.heading = new Vector(1, 0);
}

/**
 * Given a new heading, figures out how much rotation is required/allowed
 * between new heading and current heading, and then moves us forward.
 *
 * Also wraps us around the edges of the sandbox.
 */
Biod.prototype.move = function(newHeading)
{
	var newAngle, currentAngle, left, right, rotationAmount, positionOffset;

	//Rotate current heading to new heading by rotation speed.
	//Limited rotation speed gives the nice swooping effect.
	newAngle = newHeading.toDegrees();
	currentAngle = this.heading.toDegrees();

	//Figure out if it's quicker to turn left or right.
	left = (newAngle - currentAngle + 360) % 360;
	right = (currentAngle - newAngle + 360) % 360;

	//Compute how much we need to turn, capped by max turn speed.
	rotationAmount = (left < right) ? Math.min(this.turnSpeed, left) : rotationAmount = -Math.min(this.turnSpeed, right);

	//Turn.
	this.heading.fromDegrees((currentAngle + rotationAmount + 360) % 360);

	//Compute new position.
	positionOffset = this.heading.scale(this.speed);
	this.position.x = (this.position.x + positionOffset.x) % this.sandboxDimensions.x;
	this.position.y = (this.position.y + positionOffset.y) % this.sandboxDimensions.y;

	//Wrap around the sandbox.
	if (this.position.x < 0) this.position.x = this.sandboxDimensions.x;
	if (this.position.y < 0) this.position.y = this.sandboxDimensions.y;
}

/**
 * Computes a new heading for the biod based on the rest of the flock. Computes visible neighbors,
 * calculates their forces on the new heading, takes in to account forces from emitters.
 */
Biod.prototype.calculateNewHeading = function(flock)
{
	var neighbors = new Array();
	var claustrophobia = new Vector(0,0), avgHeading = new Vector(0, 0), newHeading = new Vector(0, 0), avgPosition = new Vector(0, 0);

	var claustroCount = 0;

	//Find *visible* neighbors within the flock.
	for (var i = 0; i < flock.length; i++)
	{
		var pointOnRadii = this.position.getDirectionTo(flock[i].position).scale(this.radius).add(this.position);
		var cosDot = Math.cos(this.heading.dot(this.position.getDirectionTo(flock[i].position))); //Make sure neighbor is in front of us.

		if (flock[i].position.getDistance(this.position) <= this.sightRadius && flock[i] != this && cosDot > 0)
			neighbors.push(flock[i]);
	}

	//Calculate repulsion factor from neighbors.
	for (var i = 0; i < neighbors.length; i++)
	{
		if (neighbors[i].position.getDistance(this.position) <= this.proximityRadius)
		{
			//Calculate radial point for proximity radius.
			var proximityPoint = this.position.getDirectionTo(neighbors[i].position);
			proximityPoint.scale(this.proximityRadius);

			//f = -kd, except we don't need the neg because we're just going to use the flipped dir.
			var dist = neighbors[i].position.getDistance(proximityPoint);
			var force = dist * this.claustrophobicSeverity;

			//Cheat to keep us from intersecting too much.
			if (dist < this.radius + (this.radius * 0.1))
				force += 1000000;

			claustrophobia = claustrophobia.add(neighbors[i].position.getDirectionTo(this.position).scale(force));
			claustroCount++;
		}

		//Also average heading and position of neighbors.
		avgHeading.inplaceAdd(neighbors[i].heading);
		avgPosition.inplaceAdd(neighbors[i].position);
	}

	//Average the repulsion strength.
	if (claustrophobia.x != 0) claustrophobia.x /= claustroCount;
	if (claustrophobia.y != 0) claustrophobia.y /= claustroCount;

	//Normalized heading of neighbors (same as avg).
	avgHeading = avgHeading.normalize();

	//Average position of neighbors.
	if (avgPosition.x != 0) avgPosition.x /= neighbors.length;
	if (avgPosition.y != 0) avgPosition.y /= neighbors.length;
	avgPosition = this.position.getDirectionTo(avgPosition);


	//Calculate emitter influences.
	for (var i = 0; i < this.emitterInfluences.length; i++)
		newHeading.inplaceAdd(this.emitterInfluences[i]);


	//Figure out which force is dominant.
	var claustroFactor = claustrophobia.length();
	var cohesionFactor = avgHeading.length() + avgPosition.length();
	var emitterFactor = newHeading.length();

	if (claustroFactor >= cohesionFactor && claustroFactor >= emitterFactor)
	{
		this.majorInfluence = "claustrophobia";
		this.majorInfluenceStrength = claustroFactor;
	}
	else
	{
		if (cohesionFactor >= emitterFactor)
		{
			this.majorInfluence = "cohesion";
			this.majorInfluenceStrength = cohesionFactor;
		}
		else
		{
			this.majorInfluence = "emitter";
			this.majorInfluenceStrength = emitterFactor;
		}
	}


	//Average all the forces to calculate a new heading.
	newHeading.inplaceAdd(avgHeading);
	newHeading.inplaceAdd(claustrophobia);
	newHeading.inplaceAdd(avgPosition);

	newHeading.x /= (3 + this.emitterInfluences.length); //3 because we have 3 major forces acting on us.
	newHeading.y /= (3 + this.emitterInfluences.length);

	newHeading = newHeading.normalize(); //Convert to a direction.

	//Make sure to clear out emitter influences list.
	this.emitterInfluences.length = 0;

	return newHeading;
}


//////////////////////////////////////////
// FLOCK CLASS							//
//////////////////////////////////////////
/**
 * Manages tracking, updating, and killing biods, emitters, predators, and their bodies.
 */
function Flock(svg)
{
	this.flock = new Array();
	this.bodies = new Array();
	this.emitters = new Array();
	this.emitterBodies = new Array();
	this.predators = new Array();
	this.predatorBodies = new Array();
	this.svg = svg;
}

Flock.prototype.addBiod = function(biod)
{
	this.flock.push(biod);

	//Add a body.
	this.bodies.push(new BiodBody(this.svg, biod, false));
}

Flock.prototype.addPredator = function(predator)
{
	this.predators.push(predator);

	//Add a body.
	this.predatorBodies.push(new BiodBody(this.svg, predator, true));
}

Flock.prototype.addEmitter = function(emitter)
{
	this.emitters.push(emitter);

	//Add a body.
	this.emitterBodies.push(new EmitterBody(this.svg, emitter));
}

/**
 * Cleans up SVG elements for everything in this flock.
 */
Flock.prototype.die = function()
{
	for (var i = 0; i < this.bodies.length; i++)
		this.bodies[i].die();

	for (var i = 0; i < this.emitterBodies.length; i++)
		this.emitterBodies[i].die();

	for (var i = 0; i < this.predatorBodies.length; i++)
		this.predatorBodies[i].die();
}

/**
 * Updates our simulation.
 *
 * - Performs user input handling (keyboard).
 * - Kills biods who are being eaten.
 * - Updates emitters.
 * - Updates predators.
 * - Updates biods.
 */
Flock.prototype.update = function()
{
	////////////////////////////
	//Handle user input.
	///////////////////////////
	//Add a predator.
	if (80 in g_keysDown) //p adds a predator at a random point.
	{
		if (!g_pIsPressed)
		{
			g_pIsPressed = true;
			var newPredator = new Predator(new Vector(BoundedRandom(0, 800), BoundedRandom(0, 600)), 10, 12, 10, 200, 40000, 200, new Vector(800,600));
			g_flock.addPredator(newPredator);
		}
	}
	else
	{
		g_pIsPressed = false;
	}

	//Add an attractive emitter.
	if (75 in g_keysDown) //k adds a permanent attractor at mouse point.
	{
		if (!g_kIsPressed)
		{
			g_kIsPressed = true;
			var newEmitter = new Emitter(g_mouseVec, BoundedRandom(3000, 6000), BoundedRandom(25, 150), "linear", false);
			g_flock.addEmitter(newEmitter);
		}
	}
	else
	{
		g_kIsPressed = false;
	}

	//Add a repulsive emitter.
	if (76 in g_keysDown) //k adds a permanent attractor at mouse point.
	{
		if (!g_lIsPressed)
		{
			g_lIsPressed = true;
			var newEmitter = new Emitter(g_mouseVec, BoundedRandom(1000, 4000), BoundedRandom(25, 150), "linear", true);
			g_flock.addEmitter(newEmitter);
		}
	}
	else
	{
		g_lIsPressed = false;
	}

	//Add a biod
	if (66 in g_keysDown) //b adds a biod at mouse point.
	{
		if (!g_bIsPressed)
		{
			g_bIsPressed = true;
			var newBiod = new Biod(g_mouseVec.add(new Vector(BoundedRandom(-10, 10), BoundedRandom(-10, 10))), 3, 10, 7, 40, 200, 20, new Vector(800, 600));
			g_flock.addBiod(newBiod);
		}
	}
	else
	{
		g_bIsPressed = false;
	}

	//Reset the simulation.
	if (82 in g_keysDown) //r resets the sim.
	{
		if (!g_rIsPressed)
		{
			g_rIsPressed = true;
			resetSim();
		}
	}
	else
	{
		g_rIsPressed = false;
	}



	///////////////////////////
	//Update sim.
	///////////////////////////
	//Kill off biods that have been eaten!
	for (var i = 0; i < this.flock.length; i++)
	{
		var isDead = false;

		for (var j = 0; j < this.predators.length; j++)
		{
			if (this.flock[i].position.getDistance(this.predators[j].position) < Math.max(this.flock[i].radius, this.predators[j].radius))
			{
				this.flock.splice(i, 1);
				this.bodies[i].die();
				this.bodies.splice(i, 1);

				isDead = true;
				break;
			}
		}

		if (isDead)
			break;
	}


	//Update emitters.
	for (var i = 0; i < this.emitters.length; i++)
		this.emitters[i].update(this.flock);

	//Update possible mouse emitter.
	if (g_mouseEmitter != null && g_mouseIsDown)
	{
		g_mouseEmitter.repel = (16 in g_keysDown) ? true : false;
		g_mouseEmitter.update(this.flock);
	}

	//Update predators.
	var newPredHeadings = new Array();
	for (var i = 0; i < this.predators.length; i++)
		newPredHeadings.push(this.predators[i].calculateNewHeading(this.flock));

	//Move the biods.
	for (var i = 0; i < this.predators.length; i++)
		this.predators[i].move(newPredHeadings[i], this.flock);




	//Calculate new headings for all biods within the flock.
	var newHeadings = new Array();
	for (var i = 0; i < this.flock.length; i++)
		newHeadings.push(this.flock[i].calculateNewHeading(this.flock));

	//Move the biods.
	for (var i = 0; i < this.flock.length; i++)
		this.flock[i].move(newHeadings[i]);

	//Update the bodies.
	for (var i = 0; i < this.bodies.length; i++)
		this.bodies[i].update();

	for (var i = 0; i < this.emitterBodies.length; i++)
		this.emitterBodies[i].update();

	for (var i = 0; i < this.predatorBodies.length; i++)
		this.predatorBodies[i].update();
}


//////////////////////////////////////////
// BIOD BODY CLASS						//
//////////////////////////////////////////
function BiodBody(svg, biod, isPredator)
{
	this.svg = svg;
	this.biod = biod;
	this.isPredator = isPredator;

	this.svgBody = document.createElementNS("http://www.w3.org/2000/svg", 'circle');
	this.svgBody.setAttribute("cx", "0");
	this.svgBody.setAttribute("cy", "0");
	this.svgBody.setAttribute("r", this.biod.radius - 2); //-2 for border.
	this.svgBody.style.fill = "none";
	this.svgBody.style.stroke = "#000";
	this.svgBody.style.strokeWidth = "2px";

	this.svgHeading = document.createElementNS("http://www.w3.org/2000/svg", 'line');
	this.svgHeading.setAttribute("x1", "0");
	this.svgHeading.setAttribute("y1", "0");
	this.svgHeading.setAttribute("x2", "10");
	this.svgHeading.setAttribute("y2", "10");
	this.svgHeading.style.stroke = "black";
	this.svgHeading.style.strokeWidth = "1px";

	//Add to document.
	this.svg.appendChild(this.svgBody);
	this.svg.appendChild(this.svgHeading);
}

BiodBody.prototype.die = function()
{
	this.svg.removeChild(this.svgBody);
	this.svg.removeChild(this.svgHeading);
}

BiodBody.prototype.update = function()
{
	this.svgBody.setAttribute("cx", this.biod.position.x);
	this.svgBody.setAttribute("cy", this.biod.position.y);

	this.svgHeading.setAttribute("x1", this.biod.position.x);
	this.svgHeading.setAttribute("y1", this.biod.position.y);

	var dir = this.biod.position.add(this.biod.heading.scale(this.biod.radius * 2 - 4));
	this.svgHeading.setAttribute("x2", dir.x);
	this.svgHeading.setAttribute("y2", dir.y);

	//Cohesion = green.
	//Claustrophobia = red.
	//Emitter = blue.
	//Predator = purple.
	if (this.isPredator)
	{
		this.svgBody.style.fill = "#BE81F7";
	}
	else
	{
		if (this.biod.majorInfluence == "cohesion")
		{
			this.svgBody.style.fill = "#A5DF00";
		}
		else
		{
			if (this.biod.majorInfluence == "claustrophobia")
				this.svgBody.style.fill = "#FE642E";
			else
				this.svgBody.style.fill = "#58D3F7";
		}
	}
}


//////////////////////////////////////////
// EMITTER CLASS						//
//////////////////////////////////////////
/**
 * Emitters emit a radial force which can either attract or repel
 * biods. Emitters have various function typs (linear, log, exp)
 * and can stack with each other.
 */
function Emitter(position, strength, radius, functionType, repel)
{
	this.position = position;
	this.strength = strength;
	this.radius = radius;
	this.functionType = functionType;
	this.repel = repel;
}

Emitter.prototype.update = function(flock)
{
	//Affect any biods within range.
	for (var i = 0; i < flock.length; i++)
	{
		var distance = flock[i].position.getDistance(this.position);

		if (distance <= this.radius)
		{
			var subAmount = 0;

			switch(this.functionType)
			{
				case "linear":
					subAmount = Math.min(this.strength, distance);
					break;

				case "log":
					subAmount = Math.max(0, Math.log(distance));
					break;

				case "exp":
					subAmount = Math.max(0, distance * distance);
					break;
			}

			var influenceStrength = this.strength - subAmount;

			if (influenceStrength < 0) influenceStrength = 0;

			//Add to the biod's current tick.
			if (this.repel)
				flock[i].emitterInfluences.push(this.position.getDirectionTo(flock[i].position).scale(influenceStrength));
			else
				flock[i].emitterInfluences.push(flock[i].position.getDirectionTo(this.position).scale(influenceStrength));
		}
	}
}

//////////////////////////////////////////
// EMITTER BODY CLASS					//
//////////////////////////////////////////
function EmitterBody(svg, emitter)
{
	this.svg = svg;
	this.emitter = emitter;

	this.svgBody = document.createElementNS("http://www.w3.org/2000/svg", 'circle');
	this.svgBody.setAttribute("cx", "0");
	this.svgBody.setAttribute("cy", "0");
	this.svgBody.setAttribute("r", this.emitter.radius);
	this.svgBody.style.fill = "none";
	this.svgBody.style.stroke = "#000";
	this.svgBody.style.strokeWidth = "2px";

	//Add to document.
	this.svg.appendChild(this.svgBody);
}

EmitterBody.prototype.die = function()
{
	this.svg.removeChild(this.svgBody);
}


EmitterBody.prototype.update = function()
{
	this.svgBody.setAttribute("cx", this.emitter.position.x);
	this.svgBody.setAttribute("cy", this.emitter.position.y);
	this.svgBody.setAttribute("r", this.emitter.radius)


	if (!this.emitter.repel)
	{
		this.svgBody.style.fill = "#58D3F7";
		this.svgBody.style.stroke = "#58D3F7";
	}
	else
	{
		this.svgBody.style.fill = "#FE642E";
		this.svgBody.style.stroke = "#FE642E";
	}
	
	this.svgBody.setAttribute("fill-opacity", "0.05");
	this.svgBody.setAttribute("stroke-opacity", "0.3");
}


//////////////////////////////////////////
// PREDATOR CLASS						//
//////////////////////////////////////////
/**
 * Predators are moving repulsor emitters (that's how we get that nice dispersion effect which
 * looks like biods are running away!). Predators run around and chase the closest visible biod
 * (like biods, they only see what's in front of them). If a predator overlaps a biod, it "eats"
 * the biod, and the biod is removed from the simulation.
 */
function Predator(position, speed, turnSpeed, radius, sightRadius, scariness, presence, sandboxDimensions)
{
	this.position = position;
	this.speed = speed;
	this.turnSpeed = turnSpeed;
	this.radius = radius;
	this.sightRadius = sightRadius;
	this.scariness = scariness; //Strength of the repulsor emitter.
	this.presence = presence; //Radius of the repulsor emitter.

	this.sandboxDimensions = sandboxDimensions;

	this.emitter = new Emitter(this.position, this.scariness, this.presence, "exp", true);

	this.heading = new Vector(1, 0);
}

Predator.prototype.calculateNewHeading = function(flock)
{
	if (flock.length == 0)
		return this.heading;

	var victim = null;
	var distanceToVictim = this.sightRadius + 1;

	//Find the closest biod - and chase it!
	for (var i = 0; i < flock.length; i++)
		if (flock[i].position.getDistance(this.position) < distanceToVictim)
		{
			var cosDot = Math.cos(this.heading.dot(this.position.getDirectionTo(flock[i].position))); //Make sure neighbor is in front of us.

			if (cosDot > 0) //Victim must be in front of us.
			{
				victim = flock[i];
				distanceToVictim = victim.position.getDistance(this.position);
			}
		}

	//The case is on!
	if (victim != null)
		return this.position.getDirectionTo(victim.position);
	else
		return this.heading;
}

Predator.prototype.move = function(newHeading, flock)
{
	var newAngle, currentAngle, left, right, rotationAmount;
	var positionOffset;

	//Attempt to rotate current heading to new heading. Limited rotation speed is important!
	newAngle = newHeading.toDegrees();
	currentAngle = this.heading.toDegrees();

	//Figure out if it's quicker to turn left or right.
	left = (newAngle - currentAngle + 360) % 360;
	right = (currentAngle - newAngle + 360) % 360;

	//Compute how much we need to turn, capped by max turn speed.
	rotationAmount = (left < right) ? Math.min(this.turnSpeed, left) : rotationAmount = -Math.min(this.turnSpeed, right);

	//Turn.
	this.heading.fromDegrees((currentAngle + rotationAmount + 360) % 360);

	//Compute new position.
	positionOffset = this.heading.scale(this.speed);
	this.position.x = (this.position.x + positionOffset.x) % this.sandboxDimensions.x;
	this.position.y = (this.position.y + positionOffset.y) % this.sandboxDimensions.y;

	//Wrap around the sandbox.
	if (this.position.x < 0) this.position.x = this.sandboxDimensions.x;
	if (this.position.y < 0) this.position.y = this.sandboxDimensions.y;

	//Update the emitter.
	this.emitter.position = this.position;
	this.emitter.update(flock);
}


/**
 * Sets up the svg environment and hooks in mouse event listeners.
 * Also kicks off the simulation, which runs at a fixed timestep of
 * one step per 50ms.
 */
function Init()
{
	//Init stuff.
	g_svg = document.getElementsByTagName('svg')[0];

	g_svg.addEventListener("mousedown", runFromTheMouse);
	g_svg.addEventListener("mouseup", stopRunFromTheMouse);
	g_svg.addEventListener("mousemove", updateRunningFromTheMouse);

	
	resetSim();


	//Start the simulation.
	g_simulationInterval = setInterval(runSimulation, 50); //Why 20? Less CPU, is fast enough for bullets to track properly.
}

/**
 * Resets the simulation state.
 */
function resetSim()
{
	//If a sim is already running, make sure to remove all svg elements.
	if (g_flock != null)
		g_flock.die();

	g_flock = new Flock(g_svg);

	//Create a bunch of biods!
	var numBiods = 50;
	var size = 7;
	var prox = 40;
	var speed = 3;
	var turnSpeed = 10;
	var sightRadius = 200;
	var claus = 20;

	var sandboxDims = new Vector(800, 600);

	for (var i = 0; i < numBiods; i++)
	{	
		//position, speed, turnSpeed, radius, proximityRadius, sightRadius, claustrophobicSeverity, sandboxDimensions
		var newBiod = new Biod(new Vector(BoundedRandom(0, sandboxDims.x), BoundedRandom(0, sandboxDims.y)),
							   speed, turnSpeed, size, prox, sightRadius, claus, sandboxDims);

		//Add the biod to the flock.
		g_flock.addBiod(newBiod);
	}
}

/**
 * Updates the simulation (one step).
 */
function runSimulation()
{
	//Update the flock.
	g_flock.update();
}


/**
 * Generates a random number between a min and max value.
 */
function BoundedRandom(min, max)
{
	return (Math.random() * (max - min)) + min;
}


function runFromTheMouse(event)
{
	g_mouseIsDown = true;

	g_mouseEmitter = new Emitter(new Vector(event.x, event.y), 4000, 200, "linear", true);
}

function stopRunFromTheMouse(event)
{
	g_mouseIsDown = false;
}

function updateRunningFromTheMouse(event)
{
	if (g_mouseIsDown)
		g_mouseEmitter.position = new Vector(event.x, event.y);

	g_mouseVec = new Vector(event.x, event.y);
}


/**
 * Manages tracking all keydown events (key presses).
 */
addEventListener("keydown", 
	function (e)
	{
		g_keysDown[e.keyCode] = true;
	}, false
);

/**
 * Cancels all keypresses (keyup events).
 */
addEventListener("keyup",
	function (e)
	{
		delete g_keysDown[e.keyCode];
	}, false
);