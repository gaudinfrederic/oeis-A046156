import A046156Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- Certificat bassin A046156, tranche 0 : atteint ATT en <=32
    pas (decide kernel, 1001 multisets total). -/
theorem basin_chunk156_0 :
    ((genMultisets 4 0).take 500).all (fun M => reachesATT156 32 M) = true := by
  decide
