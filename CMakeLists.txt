cmake_minimum_required(VERSION 3.20)

include(/Users/lemouton/Projets/MAXMSPStuff/_SDKS/max-sdk/source/max-sdk-base/script/max-pretarget.cmake)

#############################################################
# MAX EXTERNAL
#############################################################

include_directories( 
	"${MAX_SDK_INCLUDES}"
	"${MAX_SDK_MSP_INCLUDES}"
	"${MAX_SDK_JIT_INCLUDES}"
)

file(GLOB PROJECT_SRC
     "*.h"
	 "*.c"
     "*.cpp"
)
add_library( 
	${PROJECT_NAME} 
	MODULE
	${PROJECT_SRC}
)

include(/Users/lemouton/Projets/MAXMSPStuff/_SDKS/max-sdk/source/max-sdk-base/script/max-posttarget.cmake)
