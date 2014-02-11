#ifndef ROSE_SAGESUPPORT_CMDLINE_H
#define ROSE_SAGESUPPORT_CMDLINE_H

/**
 * \file    cmdline.h
 * \author  Justin Too <too1@llnl.gov>
 * \date    April 4, 2012
 */

/*-----------------------------------------------------------------------------
 *  Dependencies
 *---------------------------------------------------------------------------*/
// tps (01/14/2010) : Switching from rose.h to sage3.
#include "sage_support.h"

namespace Rose {
namespace Cmdline {
  /** Constants to be used with CommandlineProcessing::isOptionWithParameter
   *  to specify the removeOption argument.
   */
  enum {
    KEEP_OPTION_IN_ARGV = 0,      ///< Don't remove the CLI option from the input argv
    REMOVE_OPTION_FROM_ARGV = 1   ///< Remove the CLI option from the input argv
  };

  void
  makeSysIncludeList(
      const Rose_STL_Container<string> &dirs,
      Rose_STL_Container<string> &result);

  //! Convert `-I <path>` to `-I<path>`
  //
  // TOO1 (11/21/2013): Current CLI handling assumes that there is no space
  // between the -I option and its <path> option. That is,
  //
  //      +----------+------------+
  //      | Valid    |  -I<path>  |
  //      +----------+------------+
  //      | Invalid  |  -I <path> |
  //      +----------+------------+
  //
  // Note: Path argument is validated for existence.
  //
  std::vector<std::string>
  NormalizeIncludePathOptions (std::vector<std::string>& argv);

  /** Removes "-rose:" options, or transforms them into their associated
   *  compiler options.
   *
   *  For example,
   *
   *      -rose:java:classpath "/some/class/path"
   *
   *      becomes
   *
   *      -classpath "/some/class/path"
   *
   *  Whereas, this ROSE-only option is completely removed:
   *
   *      -rose:verose 3
   */
  void
  StripRoseOptions (std::vector<std::string>& argv);

  void
  ProcessKeepGoing (SgProject* project, std::vector<std::string>& argv);

  namespace Fortran {
    /** Targeted for src/frontend/OpenFortranParser_SAGE_Connection/jserver.C,
     */
    namespace OpenFortranParser {
      extern std::list<std::string> jvm_options;

      std::string
      GetRoseClasspath();
    } // namespace Rose::Cmdline::Fortran::OpenFortranParser
  } // namespace Rose::Cmdline::Fortran

  namespace Java {
    static const std::string option_prefix = "-rose:java:";

    /** @returns true if the Java option requires a user-specified argument.
     */
    bool
    OptionRequiresArgument (const std::string& option);

    void
    StripRoseOptions (std::vector<std::string>& argv);

    /** Process all Java commandline options.
     */
    void
    Process (SgProject* project, std::vector<std::string>& argv);

    // -rose:java
    void
    ProcessJavaOnly (SgProject* project, std::vector<std::string>& argv);

    /** Specify colon-separated Java classpath; where to search for user class files.
     *
     * Four forms are currently supported:
     * 1. `-rose:java:classpath <path1:path2:...:pathN>`
     * 1. `-rose:java:cp <path1:path2:...:pathN>`
     * 2. `-classpath `<path1:path2:...:pathN>`
     * 3. `-cp `<path1:path2:...:pathN>`
     *
     * See `man javac(1)`:
     *
     * > -cp path or -classpath path
     * >     Specify where to find user class files, and (optionally) annotation
     * >     processors and source files. This class path overrides the user class
     * >     path in the CLASSPATH environment variable.  If  neither CLASSPATH,
     * >     -cp nor -classpath is specified, the user class path consists of the
     * >     current directory. See Setting the Class Path for more details.
     *
     * >     If the -sourcepath option is not specified, the user class path is
     * >     also searched for source files.
     *
     * >     If the -processorpath option is not specified, the class path is also
     * >     searched for annotation processors.
     */
    void
    ProcessClasspath (SgProject* project, std::vector<std::string>& argv);

    /** Specify colon-separated Java sourcepath; where to search for source files.
     *
     * Two forms are currently supported:
     * 1. `-rose:java:sourcepath <path1:path2:...:pathN>`
     * 2. `-sourcepath `<path1:path2:...:pathN>`
     *
     * A sanity check is performed on every path argument. If a path does
     * not exist, a non-fatal warning will be emitted.
     *
     * See `man javac(1)`:
     *
     * > Specify the source code path to search for class or interface
     * > definitions. As with the user class path, source path entries are
     * > separated by colons (:) and can be directories, JAR archives, or
     * > ZIP archives. If packages are used, the local path name within the
     * > directory or archive must reflect the package name.
     */
    void
    ProcessSourcepath (SgProject* project, std::vector<std::string>& argv);

    /** Specify the destination directory for class files.
     *
     * See `man javac(1)`:
     *
     * > -d directory
     * >    Set the destination directory for class files. The directory must
     * >    already exist; javac will not create it. If a class is part of a
     * >    package, javac puts the class file in a subdirectory reflecting
     * >    the package name, creating directories  as  needed.  For  example,
     * >    if  you  specify  -d  /home/myclasses  and  the  class  is  called
     * >    com.mypackage.MyClass,  then  the  class  file  is  called
     * >    /home/myclasses/com/mypackage/MyClass.class.
     *
     * >    If -d is not specified, javac puts each class files in the same
     * >    directory as the source file from which it was generated.
     * >    Note: The directory specified by -d is not automatically added to
     * >    your user class path.
     */
    void
    ProcessDestdir (SgProject* project, std::vector<std::string>& argv);

    /** Specify the destination directory for class files.
     *
     * See `man javac(1)`:
     *
     * > -d directory
     * >    Set the destination directory for class files. The directory must
     * >    already exist; javac will not create it. If a class is part of a
     * >    package, javac puts the class file in a subdirectory reflecting
     * >    the package name, creating directories  as  needed.  For  example,
     * >    if  you  specify  -d  /home/myclasses  and  the  class  is  called
     * >    com.mypackage.MyClass,  then  the  class  file  is  called
     * >    /home/myclasses/com/mypackage/MyClass.class.
     *
     * >    If -d is not specified, javac puts each class files in the same
     * >    directory as the source file from which it was generated.
     * >    Note: The directory specified by -d is not automatically added to
     * >    your user class path.
     */
    void
    ProcessSourceDestdir (SgProject* project, std::vector<std::string>& argv);

    /** Targeted for src/frontend/ECJ_ROSE_Connection/jserver.C,
     */
    namespace Ecj {
      extern std::list<std::string> jvm_options;

      void
      StripRoseOptions (std::vector<std::string>& argv);

      std::string
      GetRoseClasspath();

      void
      Process (SgProject* project, std::vector<std::string>& argv);

      /** -rose:java:ecj:jvm_options
       */
      void
      ProcessJvmOptions (SgProject* project, std::vector<std::string>& argv);

      /** -rose:java:ecj:enable_remote_debugging
       *  Enable remote debugging of the Java Virtual Machine (JVM).
       */
      void
      ProcessEnableRemoteDebugging (SgProject* project, std::vector<std::string>& argv);
    }
  } // namespace Rose::Cmdline::Java

  namespace X10 {
    static std::string option_prefix = "-rose:x10:";

    void
    Process (SgProject* project, std::vector<std::string>& argv);

    // -rose:x10
    void
    ProcessX10Only (SgProject* project, std::vector<std::string>& argv);
  } // namespace Rose::Cmdline::X10

} // namespace Rose::Cmdline
} // namespace Rose
#endif // ROSE_SAGESUPPORT_CMDLINE_H

