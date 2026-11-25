/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientTree
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Context

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache

def row48Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-1152)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (220800)) (.leaf (0))) (.node 1 (.leaf (-16839680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (682007040)) (.leaf (0))) (.node 1 (.leaf (-16974397440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (283420999680)) (.leaf (0))) (.node 1 (.leaf (-3363677798400)) (.leaf (0))))))

def row48Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (29544303329280)) (.leaf (0))) (.node 1 (.leaf (-197734422282240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1030300410839040)) (.leaf (0))) (.node 1 (.leaf (-4246086541639680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (13999778090188800)) (.leaf (0))) (.node 1 (.leaf (-37217871599763456)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (80146421910601728)) (.leaf (0))) (.node 1 (.leaf (-140025932533465088)) (.leaf (0))))))

def row48Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (198181864190509056)) (.leaf (0))) (.node 1 (.leaf (-226089827240509440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (205992953708019712)) (.leaf (0))) (.node 1 (.leaf (-147682003796361216)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (81414437990301696)) (.leaf (0))) (.node 1 (.leaf (-33284415996035072)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (9499780463984640)) (.leaf (0))) (.node 1 (.leaf (-1688849860263936)) (.leaf (0))))))

def row48Part03 : LookupTree ℤ := (.leaf (140737488355328))

def row48 : CoefficientRow := ⟨49, (.node 32 (.node 16 row48Part00 row48Part01) (.node 16 row48Part02 row48Part03))⟩

theorem row48_represents : RowRepresents row48 Data.chebyshevRow48 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row49Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (49))) (.node 1 (.leaf (0)) (.leaf (-19600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2344160))) (.node 1 (.leaf (0)) (.leaf (-132612480))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4332007680))) (.node 1 (.leaf (0)) (.leaf (-91365980160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1335348940800))) (.node 1 (.leaf (0)) (.leaf (-14192851599360))))))

def row49Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (113542812794880))) (.node 1 (.leaf (0)) (.leaf (-701176668487680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3405715246940160))) (.node 1 (.leaf (0)) (.leaf (-13192098584985600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (41159347585155072))) (.node 1 (.leaf (0)) (.leaf (-104129631497486336)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (214414709191868416))) (.node 1 (.leaf (0)) (.leaf (-359663383160553472))))))

def row49Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (490450067946209280))) (.node 1 (.leaf (0)) (.leaf (-540731503483551744)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (477402588661153792))) (.node 1 (.leaf (0)) (.leaf (-332442288460398592))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (178383666978750464))) (.node 1 (.leaf (0)) (.leaf (-71116412084551680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (19826393672056832))) (.node 1 (.leaf (0)) (.leaf (-3448068464705536))))))

def row49Part03 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (281474976710656)))

def row49 : CoefficientRow := ⟨50, (.node 32 (.node 16 row49Part00 row49Part01) (.node 16 row49Part02 row49Part03))⟩

theorem row49_represents : RowRepresents row49 Data.chebyshevRow49 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row50Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (1250)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-260000)) (.leaf (0))) (.node 1 (.leaf (21528000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-947232000)) (.leaf (0))) (.node 1 (.leaf (25638412800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-466152960000)) (.leaf (0))) (.node 1 (.leaf (6034375680000)) (.leaf (0))))))

def row50Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-57930006528000)) (.leaf (0))) (.node 1 (.leaf (424820047872000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2432653747814400)) (.leaf (0))) (.node 1 (.leaf (11057517035520000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-40383975260160000)) (.leaf (0))) (.node 1 (.leaf (119536566770073600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-288405684905574400)) (.leaf (0))) (.node 1 (.leaf (568855350917201920)) (.leaf (0))))))

def row50Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-917508630511616000)) (.leaf (0))) (.node 1 (.leaf (1206989963132928000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1287455960675123200)) (.leaf (0))) (.node 1 (.leaf (1102487181118668800)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-746299014911098880)) (.leaf (0))) (.node 1 (.leaf (390051749953536000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-151732604633088000)) (.leaf (0))) (.node 1 (.leaf (41341637204377600)) (.leaf (0))))))

def row50Part03 : LookupTree ℤ := (.node 1 (.leaf (-7036874417766400)) (.node 1 (.leaf (0)) (.leaf (562949953421312))))

def row50 : CoefficientRow := ⟨51, (.node 32 (.node 16 row50Part00 row50Part01) (.node 16 row50Part02 row50Part03))⟩

theorem row50_represents : RowRepresents row50 Data.chebyshevRow50 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row51Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-51))) (.node 1 (.leaf (0)) (.leaf (22100)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2864160))) (.node 1 (.leaf (0)) (.leaf (175668480))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-6226471680))) (.node 1 (.leaf (0)) (.leaf (142642805760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2267654860800))) (.node 1 (.leaf (0)) (.leaf (26261602959360))))))

def row51Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-229402825850880))) (.node 1 (.leaf (0)) (.leaf (1550816764231680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8271022742568960))) (.node 1 (.leaf (0)) (.leaf (35307132656025600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-121927298105475072))) (.node 1 (.leaf (0)) (.leaf (343202765037633536)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-791226079003017216))) (.node 1 (.leaf (0)) (.leaf (1497374084994957312))))))

def row51Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2325467328969441280))) (.node 1 (.leaf (0)) (.leaf (2954711429749407744)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3052314510011400192))) (.node 1 (.leaf (0)) (.leaf (2537416650697736192))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1670981696800948224))) (.node 1 (.leaf (0)) (.leaf (851219911991623680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-323291602938232832))) (.node 1 (.leaf (0)) (.leaf (86131342873460736))))))

def row51Part03 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-14355223812243456))) (.node 1 (.leaf (0)) (.leaf (1125899906842624))))

def row51 : CoefficientRow := ⟨52, (.node 32 (.node 16 row51Part00 row51Part01) (.node 16 row51Part02 row51Part03))⟩

theorem row51_represents : RowRepresents row51 Data.chebyshevRow51 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row52Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-1352)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (304200)) (.leaf (0))) (.node 1 (.leaf (-27256320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1298568960)) (.leaf (0))) (.node 1 (.leaf (-38091356160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (751438571520)) (.leaf (0))) (.node 1 (.leaf (-10569685401600)) (.leaf (0))))))

def row52Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (110453212446720)) (.leaf (0))) (.node 1 (.leaf (-883625699573760)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5534287276277760)) (.leaf (0))) (.node 1 (.leaf (-27599562520657920)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (110998240572211200)) (.leaf (0))) (.node 1 (.leaf (-363391162981023744)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (974811214980841472)) (.leaf (0))) (.node 1 (.leaf (-2151307508923236352)) (.leaf (0))))))

def row52Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (3912256800501530624)) (.leaf (0))) (.node 1 (.leaf (-5857924621071810560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (7196878820173938688)) (.leaf (0))) (.node 1 (.leaf (-7207116201141469184)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (5821132316306571264)) (.leaf (0))) (.node 1 (.leaf (-3732015143555432448)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1854172428616335360)) (.leaf (0))) (.node 1 (.leaf (-687924843080843264)) (.leaf (0))))))

def row52Part03 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (179299560164687872)) (.leaf (0))) (.node 1 (.leaf (-29273397577908224)) (.node 1 (.leaf (0)) (.leaf (2251799813685248)))))

def row52 : CoefficientRow := ⟨53, (.node 32 (.node 16 row52Part00 row52Part01) (.node 16 row52Part02 row52Part03))⟩

theorem row52_represents : RowRepresents row52 Data.chebyshevRow52 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row53Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (53))) (.node 1 (.leaf (0)) (.leaf (-24804)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3472560))) (.node 1 (.leaf (0)) (.leaf (-230181120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (8823609600))) (.node 1 (.leaf (0)) (.leaf (-218825518080)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3770532003840))) (.node 1 (.leaf (0)) (.leaf (-47400973762560))))))

def row53Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (450309250744320))) (.node 1 (.leaf (0)) (.leaf (-3318068163379200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (19339597295124480))) (.node 1 (.leaf (0)) (.leaf (-90506257697341440))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (343923779249897472))) (.node 1 (.leaf (0)) (.leaf (-1069985090999681024)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2740848508964700160))) (.node 1 (.leaf (0)) (.leaf (-5799989102841430016))))))

def row53Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (10149980929972502528))) (.node 1 (.leaf (0)) (.leaf (-14670560671893028864)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (17446072150359277568))) (.node 1 (.leaf (0)) (.leaf (-16951649052980674560))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (13313246329414090752))) (.node 1 (.leaf (0)) (.leaf (-8315250199102488576)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (4031636460170903552))) (.node 1 (.leaf (0)) (.leaf (-1461981029035147264))))))

def row53Part03 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (372954344141619200)) (.leaf (0)))) (.node 1 (.leaf (-59672695062659072)) (.node 1 (.leaf (0)) (.leaf (4503599627370496)))))

def row53 : CoefficientRow := ⟨54, (.node 32 (.node 16 row53Part00 row53Part01) (.node 16 row53Part02 row53Part03))⟩

theorem row53_represents : RowRepresents row53 Data.chebyshevRow53 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row54Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (1458)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-353808)) (.leaf (0))) (.node 1 (.leaf (34201440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1758931200)) (.leaf (0))) (.node 1 (.leaf (55738575360)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1189089607680)) (.leaf (0))) (.node 1 (.leaf (18110749409280)) (.leaf (0))))))

def row54Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-205255159971840)) (.leaf (0))) (.node 1 (.leaf (1784244201062400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-12170423603036160)) (.leaf (0))) (.node 1 (.leaf (66278757110906880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-292010755966894080)) (.leaf (0))) (.node 1 (.leaf (1051238721480818688)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3114781396980203520)) (.leaf (0))) (.node 1 (.leaf (7633004526852636672)) (.leaf (0))))))

def row54Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-15512235006184390656)) (.leaf (0))) (.node 1 (.leaf (26157886481016815616)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-36538000163959996416)) (.leaf (0))) (.node 1 (.leaf (42099260501860024320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-39724430422267920384)) (.leaf (0))) (.node 1 (.leaf (30358507802383613952)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-18484672826821312512)) (.leaf (0))) (.node 1 (.leaf (8751197763422650368)) (.leaf (0))))))

def row54Part03 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-3103261618234982400)) (.node 1 (.leaf (0)) (.leaf (775182085861146624)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-121597189939003392))) (.node 1 (.leaf (0)) (.leaf (9007199254740992)))))

def row54 : CoefficientRow := ⟨55, (.node 32 (.node 16 row54Part00 row54Part01) (.node 16 row54Part02 row54Part03))⟩

theorem row54_represents : RowRepresents row54 Data.chebyshevRow54 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row55Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-55))) (.node 1 (.leaf (0)) (.leaf (27720)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4180176))) (.node 1 (.leaf (0)) (.leaf (298584000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-12341472000))) (.node 1 (.leaf (0)) (.leaf (330302668800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-6148711219200))) (.node 1 (.leaf (0)) (.leaf (83622472581120))))))

def row55Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-860819570688000))) (.node 1 (.leaf (0)) (.leaf (6886556565504000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-43680444501196800))) (.node 1 (.leaf (0)) (.leaf (223063771919155200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-927945291183685632))) (.node 1 (.leaf (0)) (.leaf (3172462533961318400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8970411302925107200))) (.node 1 (.leaf (0)) (.leaf (21065998156546703360))))))

def row55Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-41174450942341283840))) (.node 1 (.leaf (0)) (.leaf (66986333633926660096)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-90522072478279270400))) (.node 1 (.leaf (0)) (.leaf (101150170056700723200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-92762107173949931520))) (.node 1 (.leaf (0)) (.leaf (69032265803869716480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-41000982113813528576))) (.node 1 (.leaf (0)) (.leaf (18964376555880448000))))))

def row55Part03 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-6579477580611584000))) (.node 1 (.leaf (0)) (.leaf (1610036866784952320)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-247697979505377280))) (.node 1 (.leaf (0)) (.leaf (18014398509481984)))))

def row55 : CoefficientRow := ⟨56, (.node 32 (.node 16 row55Part00 row55Part01) (.node 16 row55Part02 row55Part03))⟩

theorem row55_represents : RowRepresents row55 Data.chebyshevRow55 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row56Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-1568)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (409248)) (.leaf (0))) (.node 1 (.leaf (-42561792)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (2356099200)) (.leaf (0))) (.node 1 (.leaf (-80421519360)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1849694945280)) (.leaf (0))) (.node 1 (.leaf (-30408171847680)) (.leaf (0))))))

def row56Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (372500105134080)) (.leaf (0))) (.node 1 (.leaf (-3505883342438400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (25943536734044160)) (.leaf (0))) (.node 1 (.leaf (-153639646113300480)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (738138299805204480)) (.leaf (0))) (.node 1 (.leaf (-2907129303848189952)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (9459706464902840320)) (.leaf (0))) (.node 1 (.leaf (-25573827132702851072)) (.leaf (0))))))

def row56Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (57644231319277797376)) (.leaf (0))) (.node 1 (.leaf (-108506788365699383296)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (170510667431813316608)) (.leaf (0))) (.node 1 (.leaf (-223143405458418565120)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (242024770535669366784)) (.leaf (0))) (.node 1 (.leaf (-215882722150283476992)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (156549204434560745472)) (.leaf (0))) (.node 1 (.leaf (-90753161991049707520)) (.leaf (0))))))

def row56Part03 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (41032014729995878400)) (.leaf (0))) (.node 1 (.leaf (-13934137247084314624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3341670923508908032)) (.leaf (0))) (.node 1 (.leaf (-504403158265495552)) (.node 1 (.leaf (0)) (.leaf (36028797018963968))))))

def row56 : CoefficientRow := ⟨57, (.node 32 (.node 16 row56Part00 row56Part01) (.node 16 row56Part02 row56Part03))⟩

theorem row56_represents : RowRepresents row56 Data.chebyshevRow56 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row57Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (57))) (.node 1 (.leaf (0)) (.leaf (-30856)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (4998672))) (.node 1 (.leaf (0)) (.leaf (-383707584))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (17053670400))) (.node 1 (.leaf (0)) (.leaf (-491145707520)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (9848101109760))) (.node 1 (.leaf (0)) (.leaf (-144438816276480))))))

def row57Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1605819780956160))) (.node 1 (.leaf (0)) (.leaf (-13898323250380800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (95567517969285120))) (.node 1 (.leaf (0)) (.leaf (-530343064145756160))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (2404221890794094592))) (.node 1 (.leaf (0)) (.leaf (-8986721141657698304)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (27889824232730787840))) (.node 1 (.leaf (0)) (.leaf (-72213652421952405504))))))

def row57Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (156462913580896878592))) (.node 1 (.leaf (0)) (.leaf (-283999910365325426688)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (431543407341905903616))) (.node 1 (.leaf (0)) (.leaf (-547436980973537853440))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (576811648245288665088))) (.node 1 (.leaf (0)) (.leaf (-500797710104436670464)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (354099390982935019520))) (.node 1 (.leaf (0)) (.leaf (-200470700537979863040))))))

def row57Part03 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (88643507040603340800))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-29478311360953581568)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (6931039826523193344)) (.leaf (0))) (.node 1 (.leaf (-1026820715040473088)) (.node 1 (.leaf (0)) (.leaf (72057594037927936))))))

def row57 : CoefficientRow := ⟨58, (.node 32 (.node 16 row57Part00 row57Part01) (.node 16 row57Part02 row57Part03))⟩

theorem row57_represents : RowRepresents row57 Data.chebyshevRow57 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row58Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (1682)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-470960)) (.leaf (0))) (.node 1 (.leaf (52559136)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-3123514368)) (.leaf (0))) (.node 1 (.leaf (114528860160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2831986360320)) (.leaf (0))) (.node 1 (.leaf (50104374067200)) (.leaf (0))))))

def row58Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-661377737687040)) (.leaf (0))) (.node 1 (.leaf (6717522904350720)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-53740183234805760)) (.leaf (0))) (.node 1 (.leaf (344774682051870720)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1798824428096716800)) (.leaf (0))) (.node 1 (.leaf (7715573085436379136)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-27433148748218236928)) (.leaf (0))) (.node 1 (.leaf (81353475598164426752)) (.leaf (0))))))

def row58Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-202071536163182608384)) (.leaf (0))) (.node 1 (.leaf (421432615527493140480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-738510488162464169984)) (.leaf (0))) (.node 1 (.leaf (1086230220142230372352)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1336898732482745073664)) (.leaf (0))) (.node 1 (.leaf (1369506018640860807168)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1158144624643434086400)) (.leaf (0))) (.node 1 (.leaf (798951943956919746560)) (.leaf (0))))))

def row58Part03 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-441973415805955604480)) (.leaf (0))) (.node 1 (.leaf (191221151328290996224)) (.node 1 (.leaf (0)) (.leaf (-62298293645416071168))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (14366482811311882240)) (.leaf (0)))) (.node 1 (.leaf (-2089670227099910144)) (.node 1 (.leaf (0)) (.leaf (144115188075855872))))))

def row58 : CoefficientRow := ⟨59, (.node 32 (.node 16 row58Part00 row58Part01) (.node 16 row58Part02 row58Part03))⟩

theorem row58_represents : RowRepresents row58 Data.chebyshevRow58 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row59Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-59))) (.node 1 (.leaf (0)) (.leaf (34220)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5940592))) (.node 1 (.leaf (0)) (.leaf (488825856))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-23300699136))) (.node 1 (.leaf (0)) (.leaf (720203427840)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-15512073830400))) (.node 1 (.leaf (0)) (.leaf (244647564410880))))))

def row59Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2928575256330240))) (.node 1 (.leaf (0)) (.leaf (27333369059082240)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-203047884438896640))) (.node 1 (.leaf (0)) (.leaf (1219892428249497600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-6001870746987528192))) (.node 1 (.leaf (0)) (.leaf (24417867312530456576)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-82756121729167261696))) (.node 1 (.leaf (0)) (.leaf (234920603618281259008))))))

def row59Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-560605985907262095360))) (.node 1 (.leaf (0)) (.leaf (1126865141420311707648)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1908564383666834243584))) (.node 1 (.leaf (0)) (.leaf (2719897421257998598144))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3250609113210778812416))) (.node 1 (.leaf (0)) (.leaf (3239809747386158284800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2670388640269803192320))) (.node 1 (.leaf (0)) (.leaf (1798374588451819356160))))))

def row59Part03 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-972590338652514549760)) (.leaf (0)))) (.node 1 (.leaf (411920614017535574016)) (.node 1 (.leaf (0)) (.leaf (-131527627117355335680))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (29759786337664237568)) (.leaf (0)))) (.node 1 (.leaf (-4251398048237748224)) (.node 1 (.leaf (0)) (.leaf (288230376151711744))))))

def row59 : CoefficientRow := ⟨60, (.node 32 (.node 16 row59Part00 row59Part01) (.node 16 row59Part02 row59Part03))⟩

theorem row59_represents : RowRepresents row59 Data.chebyshevRow59 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row60Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-1800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (539400)) (.leaf (0))) (.node 1 (.leaf (-64440320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (4101166080)) (.leaf (0))) (.node 1 (.leaf (-161130258432)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4272393216000)) (.leaf (0))) (.node 1 (.leaf (-81128521728000)) (.leaf (0))))))

def row60Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1150672866508800)) (.leaf (0))) (.node 1 (.leaf (-12574673417011200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (108406921352970240)) (.leaf (0))) (.node 1 (.leaf (-750870450929664000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (4238609284595712000)) (.leaf (0))) (.node 1 (.leaf (-19719314579411435520)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (76268883373279150080)) (.leaf (0))) (.node 1 (.leaf (-246865719056498950144)) (.leaf (0))))))

def row60Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (671912743399745126400)) (.leaf (0))) (.node 1 (.leaf (-1542644587342017331200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2992240771003087585280)) (.leaf (0))) (.node 1 (.leaf (-4903358987475898859520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (6776693574998742269952)) (.leaf (0))) (.node 1 (.leaf (-7870724245062418432000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (7637764119415750656000)) (.leaf (0))) (.node 1 (.leaf (-6139729224496526131200)) (.leaf (0))))))

def row60Part03 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (4038722592709594316800)) (.node 1 (.leaf (0)) (.leaf (-2136401828633320095744)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (886139521680487219200)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-277421737046022553600)) (.node 1 (.leaf (0)) (.leaf (61609242902428385280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8646911284551352320))) (.node 1 (.leaf (0)) (.leaf (576460752303423488))))))

def row60 : CoefficientRow := ⟨61, (.node 32 (.node 16 row60Part00 row60Part01) (.node 16 row60Part02 row60Part03))⟩

theorem row60_represents : RowRepresents row60 Data.chebyshevRow60 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row61Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (61))) (.node 1 (.leaf (0)) (.leaf (-37820)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (7019392))) (.node 1 (.leaf (0)) (.leaf (-617706496))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (31503031296))) (.node 1 (.leaf (0)) (.leaf (-1042463944704)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (24056860262400))) (.node 1 (.leaf (0)) (.leaf (-406904607866880))))))

def row61Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5229920989347840))) (.node 1 (.leaf (0)) (.leaf (-52482715893104640)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (419861727144837120))) (.node 1 (.leaf (0)) (.leaf (-2721633330108825600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (14479089316178952192))) (.node 1 (.leaf (0)) (.leaf (-63856496471353327616)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (235293888475725561856))) (.node 1 (.leaf (0)) (.leaf (-728652041731279159296))))))

def row61Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1904431472706752348160))) (.node 1 (.leaf (0)) (.leaf (-4212154316104346370048)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (7893045925673009414144))) (.node 1 (.leaf (0)) (.leaf (-12526615396209796317184))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (16803996263208263352320))) (.node 1 (.leaf (0)) (.leaf (-18981258237510995148800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (17945916879101304504320))) (.node 1 (.leaf (0)) (.leaf (-14077833037444871618560))))))

def row61Part03 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (9050035524071703183360)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4684724271284175765504)) (.leaf (0))) (.node 1 (.leaf (1903806670478329774080)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-584603260429709344768)) (.node 1 (.leaf (0)) (.leaf (127469883853094518784)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-17582052945254416384))) (.node 1 (.leaf (0)) (.leaf (1152921504606846976))))))

def row61 : CoefficientRow := ⟨62, (.node 32 (.node 16 row61Part00 row61Part01) (.node 16 row61Part02 row61Part03))⟩

theorem row61_represents : RowRepresents row61 Data.chebyshevRow61 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row62Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (1922)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-615040)) (.leaf (0))) (.node 1 (.leaf (78479104)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-5336579072)) (.leaf (0))) (.node 1 (.leaf (224136321024)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6357321105408)) (.leaf (0))) (.node 1 (.leaf (129242242252800)) (.leaf (0))))))

def row62Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1964482082242560)) (.leaf (0))) (.node 1 (.leaf (23034515395706880)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-213372353139179520)) (.leaf (0))) (.node 1 (.leaf (1590593905219338240)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-9681875944813363200)) (.leaf (0))) (.node 1 (.leaf (48677493211769339904)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-203981876315985805312)) (.leaf (0))) (.node 1 (.leaf (717453496007950073856)) (.leaf (0))))))

def row62Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-2129216826862303444992)) (.leaf (0))) (.node 1 (.leaf (5351507532755522027520)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-11416549403211780325376)) (.leaf (0))) (.node 1 (.leaf (20689450838821917687808)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-31829924367418334904320)) (.leaf (0))) (.node 1 (.leaf (41478716771478945136640)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-45600280594437740953600)) (.leaf (0))) (.node 1 (.leaf (42031562982699135139840)) (.leaf (0))))))

def row62Part03 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-32194388667599337553920)) (.node 1 (.leaf (0)) (.leaf (20236472876776726462464)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-10255588064248838750208))) (.node 1 (.leaf (0)) (.leaf (4085035078002682101760))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1230815763761847074816))) (.node 1 (.leaf (0)) (.leaf (263586678990740389888)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-35740566642812256256))) (.node 1 (.leaf (0)) (.leaf (2305843009213693952))))))

def row62 : CoefficientRow := ⟨63, (.node 32 (.node 16 row62Part00 row62Part01) (.node 16 row62Part02 row62Part03))⟩

theorem row62_represents : RowRepresents row62 Data.chebyshevRow62 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row63Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-63))) (.node 1 (.leaf (0)) (.leaf (41664)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8249472))) (.node 1 (.leaf (0)) (.leaf (774664704))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-42176189440))) (.node 1 (.leaf (0)) (.leaf (1490736586752)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-36771502473216))) (.node 1 (.leaf (0)) (.leaf (665389092372480))))))

def row63Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-9158885153832960))) (.node 1 (.leaf (0)) (.leaf (98551746684518400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-846606433423196160))) (.node 1 (.leaf (0)) (.leaf (5902821140547502080))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-33842841205805678592))) (.node 1 (.leaf (0)) (.leaf (161211482894892007424)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-643257641107697172480))) (.node 1 (.leaf (0)) (.leaf (2163559033747179307008))))))

def row63Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-6162865126431359238144))) (.node 1 (.leaf (0)) (.leaf (14915169381615390425088)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-30726144732096570064896))) (.node 1 (.leaf (0)) (.leaf (53905517073853631692800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-80463844998044933160960))) (.node 1 (.leaf (0)) (.leaf (101938691780468885422080)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-109146478067976786411520))) (.node 1 (.leaf (0)) (.leaf (98140959002843141898240))))))

def row63Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-73438812859270378291200))) (.node 1 (.leaf (0)) (.leaf (45157670024837628690432)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-22414982798976007274496))) (.node 1 (.leaf (0)) (.leaf (8754673416435073548288))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2589101411376788668416))) (.node 1 (.leaf (0)) (.leaf (544755410926735196160)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-72634054790231359488))) (.node 1 (.leaf (0)) (.leaf (4611686018427387904))))))

def row63 : CoefficientRow := ⟨64, (.node 32 (.node 16 row63Part00 row63Part01) (.node 16 row63Part02 row63Part03))⟩

theorem row63_represents : RowRepresents row63 Data.chebyshevRow63 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
