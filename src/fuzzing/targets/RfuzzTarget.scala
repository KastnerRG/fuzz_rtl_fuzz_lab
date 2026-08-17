// Copyright 2021 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package fuzzing.targets

import chiseltest.simulator._

class RfuzzTarget(dut: SimulatorContext, info: TopmoduleInfo) extends FuzzTarget {
  val MetaReset = "metaReset"
  require(info.clocks.size == 1, s"Only designs with a single clock are supported!\n${info.clocks}")
  require(info.inputs.exists(_._1 == MetaReset), s"No meta reset in ${info.inputs}")
  require(info.inputs.exists(_._1 == "reset"))

  private var isValid = true

  // ---------------------------------------------------------------------
  // OVTRACE recording (crv-fuzzing).
  //
  // overlap/campaign.py replays this trace in OpenTitan DV and requires it to
  // reproduce the run exactly, so the sampling point has to match the Verilator
  // wrapper's RecordInputs(): once per DUT clock, with the inputs for the
  // coming rising edge already applied. peek() after poke() and before step()
  // is that point. Enabled by TRACE_FILE; a design without a trace_i_o port
  // (every upstream rtl-fuzz-lab benchmark) is unaffected.
  // ---------------------------------------------------------------------
  private val traceEnabled =
    Option(System.getenv("TRACE_FILE")).exists(_.nonEmpty) && info.outputs.exists(_._1 == "trace_i_o")
  private val traceBits  = if (traceEnabled) info.outputs.toMap.apply("trace_i_o") else 0
  private val traceWords = (traceBits + 31) / 32
  private val traceOut = if (!traceEnabled) None else {
    val f = new java.io.File(System.getenv("TRACE_FILE"))
    val fresh = !f.exists() || f.length() == 0
    val w = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(f, true)))
    if (fresh) w.print(s"OVTRACE 1 $traceBits\n")
    Some(w)
  }
  private val traceRows = new StringBuilder
  private var traceInputCycles = 0

  // Same digit layout as the wrapper: top word bare, the rest zero-padded to 8.
  private def recordTrace(): Unit = if (traceEnabled) {
    val v = dut.peek("trace_i_o")
    traceRows.append(((v >> ((traceWords - 1) * 32)) & 0xffffffffL).toString(16))
    var i = traceWords - 2
    while (i >= 0) {
      traceRows.append(String.format("%08x", ((v >> (i * 32)) & 0xffffffffL).bigInteger))
      i -= 1
    }
    traceRows.append('\n')
  }

  // One case per AFL input, and only if the input drove at least one cycle --
  // the wrapper likewise opens a case on the first byte that arrives.
  private def flushTrace(): Unit = traceOut.foreach { w =>
    if (traceInputCycles > 0) { w.print("@ 0\n"); w.print(traceRows); w.flush() }
    traceRows.setLength(0)
    traceInputCycles = 0
  }

  private val clock = info.clocks.head
  private def step(): Unit = {
    val assert_failed = dut.peek("assert_failed") == 1
    if (assert_failed) {
      isValid = false
    }

    recordTrace()
    dut.step(1)
    cycles += 1
  }
  private var cycles:       Long = 0
  private var resetCycles:  Long = 0
  private var totalTime:    Long = 0
  private var coverageTime: Long = 0

  private def setInputsToZero(): Unit = {
    info.inputs.foreach { case (n, _) => dut.poke(n, 0) }
  }

  private def metaReset(): Unit = {
    dut.poke(MetaReset, 1)
    step()
    dut.poke(MetaReset, 0)
    resetCycles += 1
  }

  // Upstream drives reset for exactly one cycle, and steps metaReset with reset
  // still low -- so a recorded case begins with the DUT *out* of reset and gets
  // a single reset cycle. OpenTitan's DV replay environment cannot start from
  // that: its TL agent stays wedged and the replay never terminates (one 5-row
  // case ran >7 min without finishing; the same case with a proper prefix
  // verifies in seconds). RFUZZ_RESET_CYCLES holds reset for n cycles and
  // asserts it across metaReset too. Unset means upstream behaviour exactly, so
  // the bundled benchmarks are untouched.
  private val resetHold = Option(System.getenv("RFUZZ_RESET_CYCLES")).map(_.toInt).getOrElse(0)

  private def reset(): Unit = {
    dut.poke("reset", 1)
    for (_ <- 0 until math.max(resetHold, 1)) { step(); resetCycles += 1 }
    dut.poke("reset", 0)
  }

  private val inputBits = info.inputs.map(_._2).sum
  private val inputSize = scala.math.ceil(inputBits.toDouble / 8.0).toInt

  private val originalRFUZZinputSize = ((((inputBits + 7) / 8) + 8 - 1) / 8) * 8

  private def pop(input: java.io.InputStream): Array[Byte] = {
    val r = input.readNBytes(inputSize)
    if (r.size == inputSize) { r } else { Array.emptyByteArray }
  }

  private def popRFUZZ(input: java.io.InputStream): Array[Byte] = {
    val r = input.readNBytes(originalRFUZZinputSize)
    if (r.size == originalRFUZZinputSize) { r } else { Array.emptyByteArray }
  }

  private def getCoverage(feedbackCap: Int): Seq[Byte] = {
    dut.getCoverage().map(_._2).map(v => scala.math.min(v, feedbackCap).toByte)
  }

  private val fuzzInputs = info.inputs.filterNot { case (n, _) => n == MetaReset || n == "reset" }
  private def applyInputs(bytes: Array[Byte]): Unit = {
    var input: BigInt = bytes.zipWithIndex.map { case (b, i) => (0xff & BigInt(b)) << (i * 8) }.reduce(_ | _)
    fuzzInputs.foreach { case (name, bits) =>
      val mask = (BigInt(1) << bits) - 1
      val value = input & mask
      input = input >> bits
      //println("'" + name + "'", bits.toString, value.toString)
      dut.poke(name, value)
    }
    //println("---")
  }

  private def applyRfuzzInputs(bytes: Array[Byte]): Unit = {
    //Ordered Rfuzz inputs
    val sortedInputs = Seq[String]("auto_in_a_bits_data", "auto_in_c_bits_data", "auto_in_a_bits_address",
      "auto_in_c_bits_address", "auto_in_a_bits_source", "auto_in_c_bits_source", "auto_in_a_bits_mask", "auto_in_a_bits_opcode",
      "auto_in_a_bits_param", "auto_in_c_bits_opcode", "auto_in_c_bits_param", "auto_in_a_bits_size", "auto_in_c_bits_size",
      "auto_in_a_valid", "auto_in_b_ready", "auto_in_c_valid", "auto_in_c_bits_error", "auto_in_d_ready", "auto_in_e_valid",
      "auto_in_e_bits_sink", "io_port_scl_in", "io_port_sda_in")

    //Create sequence of (channel, bit size) tuples ordered by original RFUZZ ordering
    val channelNameToSize = fuzzInputs.map { input => (input._1, input._2) }.toMap
    val sortedTuples = sortedInputs.map { input => (input, channelNameToSize(input)) }

    //Iterate over bits and apply bits to dut
    var input: BigInt = bytes.reverse.zipWithIndex.map { case (b, i) => BigInt(b) << (i * 8) }.reduce(_ | _)
    sortedTuples.foreach { case (name, size) =>
      val shiftLength = originalRFUZZinputSize * 8 - size
      val mask = ((BigInt(1) << size) - 1) << shiftLength
      val bits = (input & mask) >> shiftLength
      dut.poke(name, bits)
      input = input << size
    }
  }

  override def run(input: java.io.InputStream, feedbackCap: Int): (Seq[Byte], Boolean) = {
    val start = System.nanoTime()
    setInputsToZero()
    if (resetHold > 0) dut.poke("reset", 1) // so the case starts in reset
    metaReset()
    reset()
    isValid = true
    // we only consider coverage _after_ the reset is done!
    dut.resetCoverage()

    var inputBytes = pop(input)
    while (inputBytes.nonEmpty) {
      applyInputs(inputBytes)
      step()
      traceInputCycles += 1
      inputBytes = pop(input)
    }
    flushTrace()

    val startCoverage = System.nanoTime()
    var c = getCoverage(feedbackCap)

    if (!isValid && !acceptInvalid) {
      c = Seq.fill[Byte](c.length)(0)
    }

    val end = System.nanoTime()
    totalTime += (end - start)
    coverageTime += (end - startCoverage)
    (c, isValid)
  }

  private val acceptInvalid = false

  private def ms(i: Long): Long = i / 1000 / 1000
  override def finish(verbose: Boolean): Unit = {
    traceOut.foreach(_.close())
    dut.finish()
    if (verbose) {
      println(s"Executed $cycles target cycles (incl. $resetCycles reset cycles).")
      println(s"Total time in simulator: ${ms(totalTime)}ms")
      println(s"Total time for getCoverage: ${ms(coverageTime)}ms (${coverageTime.toDouble / totalTime.toDouble * 100.0}%)")
      val MHz = cycles.toDouble * 1000.0 / totalTime.toDouble
      println(s"$MHz MHz")
    }
  }
}
