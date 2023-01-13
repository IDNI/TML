# exclude target from all and default
function(exclude target)
	set_target_properties(${target} PROPERTIES
		EXCLUDE_FROM_ALL 1
		EXCLUDE_FROM_DEFAULT_BUILD 1)
endfunction()
