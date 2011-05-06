/*
 * SHprofConverter.scala
 * 
 * Copyright (C) 2011 by Yoshi Toshima <dolphin.duke@gmail.com>
 */

package name.dd

import scala.collection.mutable.ListBuffer
import java.io.File
import java.io.FileWriter
import java.io.RandomAccessFile
import java.io.PrintWriter


class SHprofConverter extends scala.util.logging.ConsoleLogger {
  val versionString = "0.3"
  var vflag = false
  var debugFlag = false
  var dumpName = false
  var doConversion = false
  var dumpCharArray = false
  var dumpString = false
  val hprofFiles = new ListBuffer[String]
  val nameMap = scala.collection.mutable.Map.empty[Long,String]
  val cnDic = scala.collection.mutable.Map.empty[Long,Long]
  // new scala.collection.mutable.HashMap[Long,String] { override def default(key: Long) = "default value" }
  val clsDic = scala.collection.mutable.Map.empty[Long,ClassInfo]
  val emptyCharArray = new Array[Char](0)
  val charArrayMap = new scala.collection.mutable.HashMap[Long,Array[Char]] {
    override def default(key: Long) = emptyCharArray
  }
  val pendingStrings = new scala.collection.mutable.HashMap[Long,Long] 
  val includeHeaderSize = true
  object Pass extends Enumeration {
    val Initial, Scan, Process = Value
  }

  case class FileInfo(path: String,
                      randomAccessFile: RandomAccessFile,
                      buf: BufferAdapter)
  case class HprofHeader(magicString: String, pointerSize: Int, timeMs: Long)

  case class FieldSpec(ftype: Byte, name: String)

  case class ClassInfo(superid: Long, isize: Int, fieldSpecs: List[FieldSpec]) {
    override def toString: String = {
      val buf = new StringBuilder("ClassInfo {" +
                                  superid.toHexString + ", " +
                                  isize + ", ")
      fieldSpecs addString (buf, ", ")
      buf append "}"
      buf toString
    }
  }

  var pass = Pass.Initial
  var header: HprofHeader = null
  var hprofOut: PrintWriter = null
  var finfo: FileInfo = null

  def debug(s: String) {
    if (debugFlag) {
      Console println "D: " + s
    }
  }

  def readHeader {
    // magic string: "JAVA PROFILE 1.0.1" or "JAVA PROFILE 1.0.2" + NULL
    val magicStrBytes = new Array[Byte](19)
    finfo.buf.get(magicStrBytes)
    val magicString = new String(magicStrBytes, "ASCII")
    val pointerSize = finfo.buf.getInt
    val timems = finfo.buf.getLong
    header = new HprofHeader(magicString, pointerSize, timems)

    assert(magicString.startsWith("JAVA PROFILE 1.0."))
    assert(magicStrBytes(18) == 0)
  }

  def setupOutput(path: String) {
    val outFilename = path + ".txt"
    val outFile: File = new File(outFilename)
    if (outFile exists) {
      val prevName = outFilename + ".prev"
      val prevFile = new File(prevName)
      if (prevFile exists) prevFile.delete
      if (outFile.renameTo(new File(prevName))) {
        log("I: renamed " + outFilename + " to " + prevName)
      } else {
        log("E: failed to rename " + outFilename)
      }
    }
    hprofOut = new PrintWriter(new FileWriter(outFilename))
    hprofOut println Constants.asciiHprofHeader
    hprofOut println "HEAP DUMP BEGIN (0 objects, 0 bytes) Sun Mar  9 20:47:55 2008"
    hprofOut flush
  }

  def scan: Unit = {
    import Constants._
    pass = Pass.Scan
    readHeader
    if (doConversion) setupOutput(finfo.path)
    val buf = finfo.buf

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "D: Scan starts"
    }

    while (buf.position < buf.limit) {
      val tag = buf.get
      val elapsedTimeMs = buf.getInt
      val remaining = buf.getInt
      tag match {
        case HPROF_UTF8 => processUTF8(remaining)
        case HPROF_LOAD_CLASS => processLoadClass
        case HPROF_HEAP_DUMP => processHeapDump(remaining)
        case _ => buf.position(buf.position+remaining)
      }
    }
  }

  def process = {
    import Constants._
    val buf = finfo.buf
    buf.position(0)
    pass = Pass.Process
    readHeader

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "D: Process starts"
    }

    while (buf.position < buf.limit) {
      val tag = buf.get
      val elapsedTimeMs = buf.getInt
      val remaining = buf.getInt
      tag match {
        case HPROF_UTF8 => processUTF8(remaining)
        case HPROF_LOAD_CLASS => processLoadClass
        case HPROF_HEAP_DUMP => processHeapDump(remaining)
        case _ => buf.position(buf.position+remaining)
      }
    }
  }

  def processUTF8(remaining: Int) {
    assert(remaining >= 4)
    val balen = remaining - header.pointerSize
    val buf = finfo.buf
    debug("RECORD UTF8 @0x" + (buf.position-Constants.RECORD_HEADER_SIZE).toHexString)
    val nameid = readId
    if (balen > 0) {
      val currentOffset = buf.position
      try {
        val utf8a = new Array[Byte](remaining - header.pointerSize)
        buf get utf8a
        val str = new String(utf8a, "UTF8")
        nameMap(nameid) = str
        if (dumpName) {
          Console.printf("name %x %s\n", nameid, str)
        }
      } catch {
        case ex: OutOfMemoryError => log("OOM in processUTF8")
      }
    }
  }

  def processLoadClass {
    val buf = finfo.buf
    debug("RECORD LOAD_CLASS @0x" + 
        (buf.position-Constants.RECORD_HEADER_SIZE).toHexString)
    val serial = buf getInt
    val objId = readId
    val stktsn = buf getInt
    val nameid = readId
    cnDic(objId) = nameid
  }

  def processHeapDump(remaining: Int) {
    import Constants._
    val buf = finfo.buf
    debug("RECORD HEAP_DUMP @0x" + 
        (buf.position-Constants.RECORD_HEADER_SIZE).toHexString)
    val endpos = buf.position + remaining
    var nProcessed: Long = 0
    var printProgress = false
    while (buf.position < endpos) {
      val subRecordType: Byte = buf.get
      subRecordType match {
        case HPROF_GC_ROOT_UNKNOWN => process_HPROF_GC_ROOT_UNKNOWN
        case HPROF_GC_ROOT_THREAD_OBJ => process_HPROF_GC_ROOT_THREAD_OBJ
        case HPROF_GC_ROOT_JNI_GLOBAL => process_HPROF_GC_ROOT_JNI_GLOBAL
        case HPROF_GC_ROOT_JNI_LOCAL => process_HPROF_GC_ROOT_JNI_LOCAL
        case HPROF_GC_ROOT_JAVA_FRAME => process_HPROF_GC_ROOT_JAVA_FRAME
        case HPROF_GC_ROOT_NATIVE_STACK => process_HPROF_GC_ROOT_NATIVE_STACK
        case HPROF_GC_ROOT_STICKY_CLASS => process_HPROF_GC_ROOT_STICKY_CLASS
        case HPROF_GC_ROOT_THREAD_BLOCK => process_HPROF_GC_ROOT_THREAD_BLOCK
        case HPROF_GC_ROOT_MONITOR_USED => process_HPROF_GC_ROOT_MONITOR_USED
        case HPROF_GC_CLASS_DUMP => process_HPROF_GC_CLASS_DUMP
        case HPROF_GC_INSTANCE_DUMP => process_HPROF_GC_INSTANCE_DUMP
        case HPROF_GC_OBJ_ARRAY_DUMP => process_HPROF_GC_OBJ_ARRAY_DUMP
        case HPROF_GC_PRIM_ARRAY_DUMP => process_HPROF_GC_PRIM_ARRAY_DUMP
        case _ => log("E: Unknown heapdump sub record type " + subRecordType)
      }
    }
  }

  def shouldLogRoot = doConversion && pass == Pass.Scan

  def process_HPROF_GC_ROOT_UNKNOWN {
    val buf = finfo.buf
    debug("RECORD GC ROOT UNKNOWN @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
          Console println "HPROF_GC_ROOT_UNKNOWN " + tid.toHexString +
  		  ", frame=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString + " (kind=<unknown>)"
    }
  }

  def process_HPROF_GC_ROOT_THREAD_OBJ {
    val buf = finfo buf

    debug("RECORD GC ROOT THREAD OBJ @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val tSeq = finfo.buf getInt
    val stkTrcSeq = finfo.buf getInt

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
          Console println "HPROF_GC_ROOT_THREAD_OBJ " + tid.toHexString +
  		  ", frame=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString +
          " (kind=<thread>, id=" + tSeq.toHexString + ", trace=0)"
    }
  }

  def process_HPROF_GC_ROOT_JNI_GLOBAL {
    val buf = finfo.buf
    debug("RECORD GC ROOT JNI GLOBAL @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val jniGrId = readId
    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "ROOT " + tid.toHexString +
                " (kind=<JNI global ref>, id=0, trace=0) " + pass
    }
    if (shouldLogRoot) {
            hprofOut println "ROOT " + tid.toHexString +
                " (kind=<JNI global ref>, id=0, trace=0)"
    }
  }

  def process_HPROF_GC_ROOT_JNI_LOCAL {
    val buf = finfo.buf
    debug("RECORD GC ROOT JNI LOCAL @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val tsn = buf getInt
    val frn = buf getInt

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "HPROF_GC_ROOT_JNI_LOCAL " + tid.toHexString +
                " (kind=<JNI global ref>, id=0, trace=0) " + pass
    }
  }

  def process_HPROF_GC_ROOT_JAVA_FRAME {
    val buf = finfo buf

    debug("RECORD GC ROOT JAVA_FRAME @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val tsn = buf getInt
    val frn = buf getInt

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "ROOT " + tid.toHexString +
              " (kind=<Java stack>, thread=" + tsn.toHexString + ", frame=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString +
        " (kind=<Java stack>, thread=" + tsn.toHexString + ", frame=0)"
    }
  }

  def process_HPROF_GC_ROOT_NATIVE_STACK {
    val buf = finfo buf

    debug("RECORD GC ROOT NATIVE STACK @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val tsn = finfo.buf getInt

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "HPROF_GC_ROOT_NATIVE_STACK " + tid.toHexString +
              " (kind=<Java stack>, thread=" + tsn.toHexString + ", frame=0) " + pass
    }
  }

  def process_HPROF_GC_ROOT_STICKY_CLASS {
    val buf = finfo buf

    debug("RECORD GC ROOT STICKY CLASS @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId

    val name = nameMap(cnDic(tid))
    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "HPROF_GC_ROOT_STICKY_CLASS " + tid.toHexString +
              " (kind=<system class>, name=" + name + ", frame=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString +
          " (kind=<system class>, name=" + name + ")"
    }
  }

  def process_HPROF_GC_ROOT_THREAD_BLOCK {
    val buf = finfo buf

    debug("RECORD GC ROOT THREAD BLOCK @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId
    val tsn = finfo.buf getInt

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "HPROF_GC_ROOT_THREAD_BLOCK " + tid.toHexString +
              " (kind=<Java stack>, thread=" + tsn.toHexString + ", frame=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString + " (kind=<thread block>, thread=" + tsn + ")"
    }
  }

  def process_HPROF_GC_ROOT_MONITOR_USED {
    val buf = finfo buf

    debug("RECORD GC ROOT MONITOR USED @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val tid = readId

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "HPROF_GC_ROOT_MONITOR_USED " + tid.toHexString +
                " (kind=<JNI global ref>, id=0, trace=0) " + pass
    }
    if (shouldLogRoot) {
      hprofOut println "ROOT " + tid.toHexString + " (kind=<busy monitor>)"
    }
  }

  def process_HPROF_GC_CLASS_DUMP {
    val buf = finfo buf

    debug("RECORD GC CLASS DUMP @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val id = readId
    val stksn = buf getInt
    val superid = readId
    val loaderid = readId
    val signersid = readId
    val domainid = readId
    readId
    readId
    val instsize = buf getInt
    val cpoolsize = buf getShort

    if (shouldLogRoot) {
      hprofOut println "CLS " + id.toHexString + " (name=" +
          nameForClassId(id)  + ", trace=0)"
      if (superid != 0) hprofOut println "\tsuper\t" + superid.toHexString
      if (loaderid != 0) hprofOut println "\tloader\t" + loaderid.toHexString
      if (domainid != 0) hprofOut println "\tdomain\t" + domainid.toHexString
    }

    for (i <- 0 until cpoolsize) {
      val cpidx = buf getShort
      val cpetype = buf get

      cpetype match {
        case 2 => readId // object
        case 4 => buf get  // boolean
        case 5 => buf getChar // char
        case 6 => buf getFloat // float
        case 7 => buf getDouble // double
        case 8 => buf get // byte
        case 9 => buf getShort // short
        case 10 => buf getInt // Int
        case 11 => buf getLong // Long
        case _ => {
          log("E: unknown constant pool entry type " + cpetype)
          System exit 1
        }
      }
    }

    val nStaticFields = buf getShort

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "CLS " + id.toHexString + " (name=" +
          nameForClassId(id)  + ", trace=0)"
      Console println "\tsuper\t" + superid.toHexString
      Console println "\tloader\t" + loaderid.toHexString
      Console println "\tdomain\t" + domainid.toHexString
      Console println "\tnStaticFields\t" + nStaticFields
    }

    for (i <- 0 until nStaticFields) {
      val nid = readId
      if (debugFlag) log("D: looking up nid " + nid)
      val fname = nameMap(nid)
      val ftype = buf get

      ftype match {
        case 2 => {
          val sfid = readId
          if (shouldLogRoot && sfid != 0) {
            hprofOut println "\tstatic " + fname + "\t" + sfid.toHexString
          }
        }
        case 4 => buf get     // boolean
        case 5 => buf getChar // char
        case 6 => buf getFloat // float
        case 7 => buf getDouble // double
        case 8 => buf get // byte
        case 9 => buf getShort // short
        case 10 => buf getInt // int
        case 11 => buf getLong // long
        case x => log("E: unknown static filed type " + ftype)
      }
    }

    val nInstanceFields = buf getShort

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
      Console println "CLS " + id.toHexString + " nStaticFields " + nStaticFields +
      " nInstanceFields " + nInstanceFields
    }

    val flb = new ListBuffer[FieldSpec]

    for (i <- 0 until nInstanceFields) {
      val fid = readId
      val fname = nameMap(fid)
      val ftype = buf get

      if (pass == Pass.Scan) {
        flb += new FieldSpec(ftype, fname)
        if (buf.isInstanceOf[LoggingBufferAdapter]) {
          Console println "  fid " + fid.toHexString +
                          " type " + ftype + " name " + fname
        }
      }
    }

    if (pass == Pass.Scan) {
      clsDic(id) = new ClassInfo(superid, instsize, flb.toList)
    }
  }
  
  def process_HPROF_GC_INSTANCE_DUMP {
    val buf = finfo buf

    debug("RECORD GC INSTANCE DUMP @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val id = readId
    val stktrcn = buf getInt
    val kid = readId
    val bytesFollow = buf getInt
    
    if (pass == Pass.Scan) {
      if (buf.isInstanceOf[LoggingBufferAdapter]) {
        Console println "OBJ " + id.toHexString +
                   " (sz=xx, trace=0, class=xx @" + kid.toHexString + ") scan "
      }
      buf get(new Array[Byte](bytesFollow))
    } else if (pass == Pass.Process) {
      val cname = nameForClassId(kid)
      if (buf.isInstanceOf[LoggingBufferAdapter]) {
        Console println "OBJ " + id.toHexString + " (sz=xx, trace=0, class=" +
                        cname + "@" + kid.toHexString + ")"
      }
      if (doConversion && pass == Pass.Process) {
        val ci = clsDic(kid)
        val isize = ci.isize + header.pointerSize * 2
        hprofOut println "OBJ " + id.toHexString + " (sz=" + isize +
                         ", trace=0, class=" + cname + "@" + kid.toHexString + ")"
      }
      var cid = kid
      while (cid != 0) {
        val ci = clsDic(cid)

        if (buf.isInstanceOf[LoggingBufferAdapter]) {
          Console println "  fieldSpecs.length " + ci.fieldSpecs.length + " cls " +
              cid.toHexString + " " + nameMap(cnDic(cid))
        }
        for (i <- 0 until ci.fieldSpecs.length) {
          val fs = ci.fieldSpecs(i)

          if (buf.isInstanceOf[LoggingBufferAdapter]) {
            Console println "  fieldSpec " + i + " " + fs.toString
          }
          fs.ftype match {
            case 2 => {
              val value = readId
              if (doConversion && pass == Pass.Process && value != 0) {
                hprofOut println "\t" + fs.name + "\t" + value.toHexString
              }
              
              if (value != 0 && dumpString && pass == Pass.Process) {                
                if (fs.name == "value") {
                  //println("DD: dumpString name=value cname=" + cname)
                }
                if (fs.name == "value" &&
                    (cname == "java.lang.String" || cname == "java/lang/String")) {
                     //
                  val ca = charArrayMap(value)
                  if (ca != emptyCharArray) {
                    val ts = new String(ca)
                    println("S: " + id.toHexString + " " + ts)
                  } else {
                    pendingStrings(id) = value
                  }
                }        
              }
            }
            case 4 => buf get // boolean
            case 5 => buf getChar
            case 6 => buf getFloat
            case 7 => buf getDouble
            case 8 => buf get  // byte 
            case 9 => buf getShort // short
            case 10 => buf getInt
            case 11 => buf getLong
            case _ :Byte => {
              log("E: unknown ci.filedSpec[i].type " + fs.ftype)
            }
          }
        }
        cid = ci.superid
      } 
    }
  }
  
  def process_HPROF_GC_OBJ_ARRAY_DUMP {
    val buf = finfo buf

    debug("RECORD GC OBJ ARRAY DUMP @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val id = readId
    val stktrcsn = buf getInt
    val n_elements = buf getInt
    val ekid = readId

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
        Console println "ARR " + id.toHexString + " (sz=xx, trace=0, nelems=" +
                 n_elements + ", elem type=xx@" + ekid.toHexString + ") " + pass
    }
    if (doConversion && pass == Pass.Process) {
      val baseSize = 4 * header.pointerSize + header.pointerSize * n_elements
      val sz = if (includeHeaderSize) header.pointerSize * 4 + baseSize else baseSize
      val name = nameForClassId(ekid) 
      hprofOut println "ARR " + id.toHexString + " (sz=" + sz + 
                       ", trace=0, nelems=" + n_elements + ", elem type=" +
                       name + "@" + ekid.toHexString + ")"
    }
    for (i <- 0 until n_elements) {
      val value = readId
      if (doConversion && pass == Pass.Process && value != 0) {
        hprofOut println "\t[" + i + "]\t" + value.toHexString
      }
    }
  }
  
  def typeNumElmsToTypeSize(etype: Int, n_elements: Int) = etype match {
    case 4 => ("boolean", n_elements)
    case 5 => ("char", 2*n_elements)
    case 6 => ("float", 4*n_elements)
    case 7 => ("double", 8*n_elements)
    case 8 => ("byte", n_elements)
    case 9 => ("short", 2*n_elements)
    case 10 => ("int", 4*n_elements)
    case 11 => ("long", 8*n_elements)
    case _ => {
        log("E: Unexpected primitive array element type " + etype)
        ("invalid", -1)
    }
  }
  
  def process_HPROF_GC_PRIM_ARRAY_DUMP {
    val buf = finfo buf

    debug("RECORD GC PRIM ARRAY DUMP @0x" + 
        (buf.position-Constants.GC_RECORD_HEADER_SIZE).toHexString)
    val id = readId
    val stktrcn = buf getInt
    val n_elements = buf getInt
    val etype = buf get
    
    val (elem_type_s, sz) = typeNumElmsToTypeSize(etype, n_elements)
    val tbuf = new Array[Byte](sz)
    buf get(tbuf)

    if (buf.isInstanceOf[LoggingBufferAdapter]) {
        Console println "ARR prim " + id.toHexString + 
                        " (sz=xx, trace=0, nelems=" + n_elements +
                        ", elem type=" + elem_type_s + ") " + pass
    }
    
    if (pass == Pass.Process && etype == 5) {
      val calen = sz / 2
      val ca = new Array[Char](calen)
      for (i <- 0 until calen) {
        ca(i) = ((0xff00 & tbuf(i*2)<<8) | tbuf(i*2+1)&0xff).asInstanceOf[Char]
      }
      if (dumpString) {
        charArrayMap(id) = ca
      }
      if (dumpCharArray) {
        val stmp = new String(ca)
        print(id.toHexString + ": " + stmp)
        print(" // " + calen + " ")
        for (i <- 0 until calen) {
          print(ca(i).toHexString + " ")
        }
        println("")
        for (i <- 0 until tbuf.length) {
          print(tbuf(i).toHexString + " ")
        }
        println("")
      }
    }
    if (doConversion && pass == Pass.Process) {
      val sz2 = if (includeHeaderSize) sz + header.pointerSize*2 + 4 else sz
      hprofOut println "ARR " + id.toHexString + " (sz=" + sz2 + 
                       ", trace=0, nelems=" + n_elements + ", elem type=" +
                       elem_type_s + ")"
    }
    
    
  }

  def nameForClassId(cid: Long) = try { nameMap(cnDic(cid)) }
      catch { case e: NoSuchElementException => "null"}

  private def readId: Long = {
    val buf = finfo.buf
    header.pointerSize match {
      case 4 => buf.getInt.asInstanceOf[Long]
      case 8 => buf.getLong
      case _ => throw new IllegalStateException("unexpected pointerSize "
                                                + header.pointerSize)
    }
  }

  def processFile(path: String) {
    import java.nio.channels.FileChannel
    val file = new File(path)
    val raf = new RandomAccessFile(file, "r")
    val buf = raf.getChannel.map(FileChannel.MapMode.READ_ONLY, 0, file.length)
    finfo = if (debugFlag) new FileInfo(path, raf, new LoggingBufferAdapter(buf))
            else new FileInfo(path, raf, new BufferAdapter(buf))
    scan
    process
    if (doConversion && pass == Pass.Process) {
      if (hprofOut != null) {
        hprofOut println "HEAP DUMP END"
        hprofOut flush()
        hprofOut close()
      }
    }
  }
  def processFiles {
    if (hprofFiles isEmpty) helpAndExit
    for (path <- hprofFiles) {
      if (new File(path).exists) processFile(path)
    }
  }
  def processArgs(args: Array[String]) {
    for (arg <- args) arg match {
      case "-v" => vflag = true
      case "-d" => debugFlag = true
      case "-dump_name" => dumpName = true
      case "-convert" => doConversion = true
      case "-dump_char_array" => dumpCharArray = true
      case "-dump_string" => dumpString = true
      case "-h" => helpAndExit
      case "-help" => helpAndExit
      case _ => hprofFiles += arg
    }
  }
  def helpAndExit {
    help
    System exit 0
  }
  def help {
    val msg = """usage: scala SHprofConverter [-convert] [-v]<binary  hprof file... >
  Options:
    -convert: convert to ascii file
    -v: verbose"""
    Console println "SHprovConverter " + versionString
    Console println msg
  }

  object Constants {
    val HPROF_UTF8: Byte = 0x01
    val HPROF_LOAD_CLASS: Byte = 0x02
    val HPROF_UNLOAD_CLASS: Byte = 0x03
    val HPROF_FRAME: Byte = 0x04
    val HPROF_TRACE: Byte = 0x05
    val HPROF_ALLOC_SITES: Byte = 0x06
    val HPROF_HEAP_SUMMARY: Byte = 0x07
    val HPROF_START_THREAD: Byte = 0x0a
    val HPROF_END_THREAD: Byte = 0x0b
    val HPROF_HEAP_DUMP: Byte = 0x0c
    val HPROF_CPU_SAMPLES: Byte = 0x0d
    val HPROF_CONTROL_SETTINGS: Byte = 0x0e
    val HPROF_LOCKSTATS_WAIT_TIME: Byte = 0x10
    val HPROF_LOCKSTATS_HOLD_TIME: Byte = 0x11
    // HPROF_GC_ROOT_UNKNOWN      : Byte = 0xff
    val HPROF_GC_ROOT_UNKNOWN: Byte = -1
    val HPROF_GC_ROOT_JNI_GLOBAL: Byte = 0x01
    val HPROF_GC_ROOT_JNI_LOCAL: Byte = 0x02
    val HPROF_GC_ROOT_JAVA_FRAME: Byte = 0x03
    val HPROF_GC_ROOT_NATIVE_STACK: Byte = 0x04
    val HPROF_GC_ROOT_STICKY_CLASS: Byte = 0x05
    val HPROF_GC_ROOT_THREAD_BLOCK: Byte = 0x06
    val HPROF_GC_ROOT_MONITOR_USED: Byte = 0x07
    val HPROF_GC_ROOT_THREAD_OBJ: Byte = 0x08
    val HPROF_GC_CLASS_DUMP: Byte = 0x20
    val HPROF_GC_INSTANCE_DUMP: Byte = 0x21
    val HPROF_GC_OBJ_ARRAY_DUMP: Byte = 0x22
    val HPROF_GC_PRIM_ARRAY_DUMP: Byte = 0x23

    val RECORD_HEADER_SIZE = 9 // tag 1 + msec elapse 4 + remaining 4
    val GC_RECORD_HEADER_SIZE = 1 // tag 1

    val asciiHprofHeader = """JAVA PROFILE 1.0.1, created Sun Mar  9 20:47:24 2008

Header for -agentlib:hprof (or -Xrunhprof) ASCII Output (JDK 5.0 JVMTI based)

@(#)jvm.hprof.txt        1.5 06/01/28

 ......... (c) 2006 ... .................. All  Rights Reserved.

WARNING!  This file format is under development, and is subject to
change without notice.

This file contains the following types of records:

THREAD START
THREAD END      mark the lifetime of Java threads

TRACE           represents a Java stack trace.  Each trace consists
                of a series of stack frames.  Other records refer to
                TRACEs to identify (1) where object allocations have
                taken place, (2) the frames in which GC roots were
                found, and (3) frequently executed methods.

HEAP DUMP       is a complete snapshot of all live objects in the Java
                heap.  Following distinctions are made:

                ROOT    root set as determined by GC
                CLS     classes 
                OBJ     instances
                ARR     arrays

SITES           is a sorted list of allocation sites.  This identifies
                the most heavily allocated object types, and the TRACE
                at which those allocations occurred.

CPU SAMPLES     is a statistical profile of program execution.  The VM
                periodically samples all running threads, and assigns
                a quantum to active TRACEs in those threads.  Entries
                in this record are TRACEs ranked by the percentage of
                total quanta they consumed; top-ranked TRACEs are
                typically hot spots in the program.

CPU TIME        is a profile of program execution obtained by measuring
                the time spent in individual methods (excluding the time
                spent in callees), as well as by counting the number of
                times each method is called. Entries in this record are
                TRACEs ranked by the percentage of total CPU time. The
                "count" field indicates the number of times each TRACE 
                is invoked.

MONITOR TIME    is a profile of monitor contention obtained by measuring
                the time spent by a thread waiting to enter a monitor.
                Entries in this record are TRACEs ranked by the percentage
                of total monitor contention time and a brief description
                of the monitor.  The "count" field indicates the number of 
                times the monitor was contended at that TRACE.

MONITOR DUMP    is a complete snapshot of all the monitors and threads in 
                the System.

HEAP DUMP, SITES, CPU SAMPLES|TIME and MONITOR DUMP|TIME records are generated 
at program exit.  They can also be obtained during program execution by typing 
Ctrl-\ (on Solaris) or by typing Ctrl-Break (on Win32).

--------
"""
  }
}

class BufferAdapter(buf: java.nio.MappedByteBuffer) {
  def get = buf.get
  def get(dst: Array[Byte]) = buf.get(dst)
  def getChar = buf.getChar
  def getDouble = buf.getDouble
  def getFloat = buf.getFloat
  def getInt = buf.getInt
  def getLong = buf.getLong
  def getShort = buf.getShort
  def position = buf.position
  def position(newPosition: Int) = buf.position(newPosition)
  def limit = buf.limit
}

class LoggingBufferAdapter(buf: java.nio.MappedByteBuffer) extends BufferAdapter(buf) {
  def addrPart = "D: @" + buf.position.toHexString + " "
  def dlog(s: String) {
    Console println addrPart + s
  }
  override def get = {
    val v = buf.get()
    dlog("get=" + v.toHexString)
    v
  }
  override def get(dst: Array[Byte]) = {
    val v = buf.get(dst)
    dlog("get[]=" + dst.map(_.toHexString).mkString(" "))
    v
  }
  override def getChar = {
    val v = buf getChar()
    dlog("getChar=" + v.toHexString)
    v
  }
  override def getDouble = {
    val v = buf.getDouble()
    dlog("getDouble=" + v)
    v
  }
  override def getFloat = {
    val v = buf.getFloat()
    dlog("getFloat=" + v)
    v
  }
  override def getInt = {
    val v = buf.getInt()
    dlog("getInt=" + v.toHexString)
    v
  }
  override def getLong = {
    val v = buf.getLong()
    dlog("getLong=" + v.toHexString)
    v
  }
  override def getShort = {
    val v = buf.getShort()
    dlog("getShort=" + v.toHexString)
    v
  }
  override def position(newPosition: Int) = {
    val v = buf.position(newPosition)
    dlog("position(" + newPosition + ")")
    v
  }
}

object SHprofConverter {
  def main(args: Array[String]): Unit = {
    val shc = new SHprofConverter
    shc processArgs args
    shc processFiles
  }
}
