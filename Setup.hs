import Distribution.Simple
import System.Process

main = defaultMainWithHooks hook where
    customPreBuild args flags = do
      system "agda -c --no-main -i/usr/share/agda-stdlib -isrc src/Example.agda"
      preBuild simpleUserHooks args flags
    hook = simpleUserHooks { preBuild = customPreBuild }
