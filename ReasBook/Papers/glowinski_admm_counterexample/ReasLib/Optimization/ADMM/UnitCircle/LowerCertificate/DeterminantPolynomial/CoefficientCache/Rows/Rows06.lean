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

def row96Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-4608)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3537408)) (.leaf (0))) (.node 1 (.leaf (-1084805120)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (177830553600)) (.leaf (0))) (.node 1 (.leaf (-18083391406080)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1248849970135040)) (.leaf (0))) (.node 1 (.leaf (-62250367742115840)) (.leaf (0))))))

def row96Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (2339576320974520320)) (.leaf (0))) (.node 1 (.leaf (-68505241293894451200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1603022646277130158080)) (.leaf (0))) (.node 1 (.leaf (-30589280626794760765440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (483886953683282338775040)) (.leaf (0))) (.node 1 (.leaf (-6431974276651629856948224)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (72657487199212855791452160)) (.leaf (0))) (.node 1 (.leaf (-704193025360646896590258176)) (.leaf (0))))))

def row96Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (5903295563406390717786882048)) (.leaf (0))) (.node 1 (.leaf (-43101423578810296577638268928)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (275712280988262690806162259968)) (.leaf (0))) (.node 1 (.leaf (-1553087671000740050629306613760)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (7737562422447276713776263462912)) (.leaf (0))) (.node 1 (.leaf (-34221414291148931156864124583936)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (134787515485011540687606478012416)) (.leaf (0))) (.node 1 (.leaf (-474035320159847350824045970980864)) (.leaf (0))))))

def row96Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1491866477453420297362910635622400)) (.leaf (0))) (.node 1 (.leaf (-4208890241697159630764260536090624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (10658712995187829592840412428500992)) (.leaf (0))) (.node 1 (.leaf (-24252110071510533301389505847099392)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (49606588782635181752842171050885120)) (.leaf (0))) (.node 1 (.leaf (-91230508105995736556951119174041600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (150813823004600861675502245595054080)) (.leaf (0))) (.node 1 (.leaf (-223947760442580232461560182776791040)) (.leaf (0))))))

def row96Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (298374843526175845432415997489315840)) (.leaf (0))) (.node 1 (.leaf (-356102377355249493849410234765803520)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (379863378829348669909599152976691200)) (.leaf (0))) (.node 1 (.leaf (-361145473205873518058981223699578880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (304910771196508236295493537067171840)) (.leaf (0))) (.node 1 (.leaf (-227582419375105740233881884756541440)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (149326008502262362890301447191134208)) (.leaf (0))) (.node 1 (.leaf (-85528050157805948774997831891025920)) (.leaf (0))))))

def row96Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (42385103337697504994191963525742592)) (.leaf (0))) (.node 1 (.leaf (-17969956488852179172484879447228416)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (6422996496015437535546804300414976)) (.leaf (0))) (.node 1 (.leaf (-1897903205388966494771695935553536)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (451173437017753268088360319057920)) (.leaf (0))) (.node 1 (.leaf (-82912272071177629291643744026624)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (11052328670739875094299381071872)) (.leaf (0))) (.node 1 (.leaf (-950737950171172051122527404032)) (.leaf (0))))))

def row96Part06 : LookupTree ℤ := (.leaf (39614081257132168796771975168))

def row96 : CoefficientRow := ⟨97, (.node 48 (.node 16 row96Part00 (.node 16 row96Part01 row96Part02)) (.node 32 (.node 16 row96Part03 row96Part04) (.node 16 row96Part05 row96Part06)))⟩

theorem row96_represents : RowRepresents row96 Data.chebyshevRow96 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row97Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (97))) (.node 1 (.leaf (0)) (.leaf (-152096)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (71485120))) (.node 1 (.leaf (0)) (.leaf (-15971818240))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (2076336371200))) (.node 1 (.leaf (0)) (.leaf (-176073324277760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (10483134845460480))) (.node 1 (.leaf (0)) (.leaf (-461257933200261120))))))

def row97Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (15574238450408816640))) (.node 1 (.leaf (0)) (.leaf (-415313025344235110400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (8947029174558664949760))) (.node 1 (.leaf (0)) (.leaf (-158571062524589144801280))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (2346851725363919343058944))) (.node 1 (.leaf (0)) (.leaf (-29365734409681862549045248)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (313909574724185427248414720))) (.node 1 (.leaf (0)) (.leaf (-2892018533587979291037007872))))))

def row97Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (23136148268703834328296062976))) (.node 1 (.leaf (0)) (.leaf (-161758616466904119001196003328)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (993868256129987469899240308736))) (.node 1 (.leaf (0)) (.leaf (-5391835883458231618076850257920))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (25933415517511299392311094411264))) (.node 1 (.leaf (0)) (.leaf (-110970894307490211353145148178432)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (423707050992235352439281474863104))) (.node 1 (.leaf (0)) (.leaf (-1447110483129817688442023316553728))))))

def row97Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4429930050397401087067418315980800))) (.node 1 (.leaf (0)) (.leaf (-12174490114974504634575869630742528)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (30073994449472578937660566199599104))) (.node 1 (.leaf (0)) (.leaf (-66831098776605730972579035999109120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (133662197553211461945158071998218240))) (.node 1 (.leaf (0)) (.leaf (-240607579464577032607297990505267200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (389705391001642800354115433801973760))) (.node 1 (.leaf (0)) (.leaf (-567497251412530529547928465813012480))))))

def row97Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (742111790308693769408829532217016320))) (.node 1 (.leaf (0)) (.leaf (-869992655124438828723512504525783040)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (912268513046086751346905695282790400))) (.node 1 (.leaf (0)) (.leaf (-853163792482537468865275185447567360))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (709021964528866754947397642700718080))) (.node 1 (.leaf (0)) (.leaf (-521226957707707452285654483282690048)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (337033972653104066891475831295574016))) (.node 1 (.leaf (0)) (.leaf (-190340510359104536316510206573936640))))))

def row97Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (93055360620006662199182767658369024))) (.node 1 (.leaf (0)) (.leaf (-38939416257093590059252501071265792)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (13743323384856561197383235672211456))) (.node 1 (.leaf (0)) (.leaf (-4011683810816189475419003836956672))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (942479342684089457963606621552640))) (.node 1 (.leaf (0)) (.leaf (-171234342114032370384596660912128)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (22575074556408194693060429348864))) (.node 1 (.leaf (0)) (.leaf (-1921282940970910186643440795648))))))

def row97Part06 : LookupTree ℤ := (.node 1 (.leaf (0)) (.leaf (79228162514264337593543950336)))

def row97 : CoefficientRow := ⟨98, (.node 48 (.node 16 row97Part00 (.node 16 row97Part01 row97Part02)) (.node 32 (.node 16 row97Part03 row97Part04) (.node 16 row97Part05 row97Part06)))⟩

theorem row97_represents : RowRepresents row97 Data.chebyshevRow97 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row98Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (4802)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3841600)) (.leaf (0))) (.node 1 (.leaf (1227775360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-209774190080)) (.leaf (0))) (.node 1 (.leaf (22236064148480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1600996618690560)) (.leaf (0))) (.node 1 (.leaf (83216637433036800)) (.leaf (0))))))

def row98Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-3262092187375042560)) (.leaf (0))) (.node 1 (.leaf (99653718194712084480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2433648696965600378880)) (.leaf (0))) (.node 1 (.leaf (48483338975912090664960)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-801029078732460628377600)) (.leaf (0))) (.node 1 (.leaf (11125677727379468543066112)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-131388956018576580889542656)) (.leaf (0))) (.node 1 (.leaf (1332012174809017751087087616)) (.leaf (0))))))

def row98Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-11687332630582349299860897792)) (.leaf (0))) (.node 1 (.leaf (89373720116217965234230394880)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-599229513922070928808554266624)) (.leaf (0))) (.node 1 (.leaf (3540824183260714990427787231232)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-18521234189363739949929963978752)) (.leaf (0))) (.node 1 (.leaf (86088245326171529941486313406464)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-356729304099991963393896774369280)) (.leaf (0))) (.node 1 (.leaf (1321449422144318055702608920707072)) (.leaf (0))))))

def row98Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-4386087443713055674246957268729856)) (.leaf (0))) (.node 1 (.leaf (13068750342491961804899097168052224)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-35007693225136838861992151689986048)) (.leaf (0))) (.node 1 (.leaf (84400098970455691176710638246297600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-183268786335846643698000243049103360)) (.leaf (0))) (.node 1 (.leaf (358554903212418660447267263170478080)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-632028981933754926890098226605588480)) (.leaf (0))) (.node 1 (.leaf (1003358542445865833169791050380738560)) (.leaf (0))))))

def row98Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1433369346351236904528272929115340800)) (.leaf (0))) (.node 1 (.leaf (1840325957972637032667069299199836160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2119848689078226327356624162028257280)) (.leaf (0))) (.node 1 (.leaf (2185682499298047020752792614265159680)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2011238356161583174026043907962306560)) (.leaf (0))) (.node 1 (.leaf (1645626348432839250128677170157977600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1191779923917677267461610413756514304)) (.leaf (0))) (.node 1 (.leaf (759595995464014082557949494482173952)) (.leaf (0))))))

def row98Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-423066124055906577627212376673615872)) (.leaf (0))) (.node 1 (.leaf (204080677728865503570850414763966464)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-84301829010202617654051806442946560)) (.leaf (0))) (.node 1 (.leaf (29384549975102088889538167279976448)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-8474541058650132218926367992971264)) (.leaf (0))) (.node 1 (.leaf (1967870957439356545218856987131904)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-353521012898804615863492702896128)) (.leaf (0))) (.node 1 (.leaf (46100887062987561437243386101760)) (.leaf (0))))))

def row98Part06 : LookupTree ℤ := (.node 1 (.leaf (-3882179963198952542083653566464)) (.node 1 (.leaf (0)) (.leaf (158456325028528675187087900672))))

def row98 : CoefficientRow := ⟨99, (.node 48 (.node 16 row98Part00 (.node 16 row98Part01 row98Part02)) (.node 32 (.node 16 row98Part03 row98Part04) (.node 16 row98Part05 row98Part06)))⟩

theorem row98_represents : RowRepresents row98 Data.chebyshevRow98 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row99Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-99))) (.node 1 (.leaf (0)) (.leaf (161700)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-79168320))) (.node 1 (.leaf (0)) (.leaf (18427368960))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2495884751360))) (.node 1 (.leaf (0)) (.leaf (220545452574720)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-13685128082841600))) (.node 1 (.leaf (0)) (.leaf (627691208066334720))))))

def row99Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-22098422825158901760))) (.node 1 (.leaf (0)) (.leaf (614620461733659279360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-13814326568489865707520))) (.node 1 (.leaf (0)) (.leaf (255537740476413326131200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3948909882828840599814144))) (.node 1 (.leaf (0)) (.leaf (51617089864440799635177472)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-576687486761338589027500032))) (.node 1 (.leaf (0)) (.leaf (5556042883206014793211183104))))))

def row99Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-46510813529868532928017858560))) (.node 1 (.leaf (0)) (.leaf (340506056699340049469656793088)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2192327283974129327516348841984))) (.node 1 (.leaf (0)) (.leaf (12473484249979661598932424720384))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-62975883896238779292171022368768))) (.node 1 (.leaf (0)) (.leaf (283147384959833271236117774991360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1137165659192219279227075023601664))) (.node 1 (.leaf (0)) (.leaf (4090009327418453799847241157967872))))))

def row99Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-13202104937823512435561332853440512))) (.node 1 (.leaf (0)) (.leaf (38311990799958428244374063966846976)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-100089380899746256661644869579571200))) (.node 1 (.leaf (0)) (.leaf (235631296717517113326000312491704320))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-500199770224904749341158558096424960))) (.node 1 (.leaf (0)) (.leaf (957717385889414353501832516846223360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1653763354869152654134311887013150720))) (.node 1 (.leaf (0)) (.leaf (2574214336304262195887510566574489600))))))

def row99Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3608850483011167578465375390447697920))) (.node 1 (.leaf (0)) (.leaf (4550644571069712894057651102925455360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5151965891202539406060154019339304960))) (.node 1 (.leaf (0)) (.leaf (5224528791078631510370860413977886720))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4731498676852033102999485458625331200))) (.node 1 (.leaf (0)) (.leaf (3812479654573385952543008823598645248)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-2720593820488458601814696658808602624))) (.node 1 (.leaf (0)) (.leaf (1709532501287132701432409195538284544))))))

def row99Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-939187608731819817453607521005600768))) (.node 1 (.leaf (0)) (.leaf (447100771714824597200953330599198720)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-182346981405261796505486848558104576))) (.node 1 (.leaf (0)) (.leaf (62780783761020367254495338396909568))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-17891561459984353895816342607495168))) (.node 1 (.leaf (0)) (.leaf (4106976256992745460822310635175936)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-729617100354017426420045835141120))) (.node 1 (.leaf (0)) (.leaf (94123057066946033061130212999168))))))

def row99Part06 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (0)) (.leaf (-7843588088912169421760851083264))) (.node 1 (.leaf (0)) (.leaf (316912650057057350374175801344))))

def row99 : CoefficientRow := ⟨100, (.node 48 (.node 16 row99Part00 (.node 16 row99Part01 row99Part02)) (.node 32 (.node 16 row99Part03 row99Part04) (.node 16 row99Part05 row99Part06)))⟩

theorem row99_represents : RowRepresents row99 Data.chebyshevRow99 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row100Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-5000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4165000)) (.leaf (0))) (.node 1 (.leaf (-1386112000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (246628928000)) (.leaf (0))) (.node 1 (.leaf (-27227833651200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2042087523840000)) (.leaf (0))) (.node 1 (.leaf (-110586893598720000)) (.leaf (0))))))

def row100Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (4517474603507712000)) (.leaf (0))) (.node 1 (.leaf (-143850563845029888000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3662889620432918937600)) (.leaf (0))) (.node 1 (.leaf (-76111992112891822080000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1312104559685287280640000)) (.leaf (0))) (.node 1 (.leaf (-19023497493037149742694400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (234623135747458180159897600)) (.leaf (0))) (.node 1 (.leaf (-2485387148331694929142087680)) (.leaf (0))))))

def row100Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (22799418396994378886283264000)) (.leaf (0))) (.node 1 (.leaf (-182395347175955031090266112000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1280241627320751027747867852800)) (.leaf (0))) (.node 1 (.leaf (-7925478751208973645460484915200)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (43468202689323063147794813419520)) (.leaf (0))) (.node 1 (.leaf (-212040013118649088525828358144000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (923024074019658505866132324352000)) (.leaf (0))) (.node 1 (.leaf (-3595780740528756614156758967910400)) (.leaf (0))))))

def row100Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (12566106098549963273941439584665600)) (.leaf (0))) (.node 1 (.leaf (-39472960218138986676021762874933248)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (111631674825053695350740279623680000)) (.leaf (0))) (.node 1 (.leaf (-284578860769948204500000377405440000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (654531379770880870350000868032512000)) (.leaf (0))) (.node 1 (.leaf (-1358954443662228159129584379363328000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2547463753712583633893763260298035200)) (.leaf (0))) (.node 1 (.leaf (-4310885252184171141438414824407040000)) (.leaf (0))))))

def row100Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (6581798018959761296303294062264320000)) (.leaf (0))) (.node 1 (.leaf (-9058026923994972189597820080095232000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (11221137831217652115471926367879168000)) (.leaf (0))) (.node 1 (.leaf (-12489614281703125832873100652943769600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (12460295938318846194767764735918080000)) (.leaf (0))) (.node 1 (.leaf (-11108623702136905456127648087408640000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8816739233064449172547628060953804800)) (.leaf (0))) (.node 1 (.leaf (-6200783636440931286187342812099379200)) (.leaf (0))))))

def row100Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (3842131126630171980492030767750184960)) (.leaf (0))) (.node 1 (.leaf (-2082455895192505138478065456775168000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (978503372439851812055958467641344000)) (.leaf (0))) (.node 1 (.leaf (-394078512785625681900511864396185600)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (134036108580690866727917044786790400)) (.leaf (0))) (.node 1 (.leaf (-37750993877408064336851542202122240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8567473526884295537508113973248000)) (.leaf (0))) (.node 1 (.leaf (-1505335087771022414277335056384000)) (.leaf (0))))))

def row100Part06 : LookupTree ℤ := (.node 2 (.node 1 (.leaf (192128294097091018664344079564800)) (.leaf (0))) (.node 1 (.leaf (-15845632502852867518708790067200)) (.node 1 (.leaf (0)) (.leaf (633825300114114700748351602688)))))

def row100 : CoefficientRow := ⟨101, (.node 48 (.node 16 row100Part00 (.node 16 row100Part01 row100Part02)) (.node 32 (.node 16 row100Part03 row100Part04) (.node 16 row100Part05 row100Part06)))⟩

theorem row100_represents : RowRepresents row100 Data.chebyshevRow100 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row101Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (101))) (.node 1 (.leaf (0)) (.leaf (-171700)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (87498320))) (.node 1 (.leaf (0)) (.leaf (-21199592960))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (2989142607360))) (.node 1 (.leaf (0)) (.leaf (-275001119877120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (17769303130521600))) (.node 1 (.leaf (0)) (.leaf (-848864995263774720))))))

def row101Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (31133372032174325760))) (.node 1 (.leaf (0)) (.leaf (-902321589423719055360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (21140105809355703582720))) (.node 1 (.leaf (0)) (.leaf (-407761724702196970291200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (6573119002199415161094144))) (.node 1 (.leaf (0)) (.leaf (-89664084850515099120566272)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1045933758256254949347295232))) (.node 1 (.leaf (0)) (.leaf (-10526817179869404651495358464))))))

def row101Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (92109650323857290700584386560))) (.node 1 (.leaf (0)) (.leaf (-705296751051250111650189017088)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (4752810538615631383012084547584))) (.node 1 (.leaf (0)) (.leaf (-28324441752397608889853394550784))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (149912289274884905587760649207808))) (.node 1 (.leaf (0)) (.leaf (-707227411197131448287774491279360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2983213807231536290959339672305664))) (.node 1 (.leaf (0)) (.leaf (-11281570808475967028160759093788672))))))

def row101Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (38334317134923438983444212022771712))) (.node 1 (.leaf (0)) (.leaf (-117257911236236401596417589716713472)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (323352730549853647363125428826931200))) (.node 1 (.leaf (0)) (.leaf (-804789018257413522326001067302584320))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1809262529766666490041160294161448960))) (.node 1 (.leaf (0)) (.leaf (-3675626273213870671761001275572879360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (6748690862294319921921838407609221120))) (.node 1 (.leaf (0)) (.leaf (-11195984840672604478764340215388569600))))))

def row101Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (16772446520930690171071963514976337920))) (.node 1 (.leaf (0)) (.leaf (-22666698419059657273253291263115919360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (27594241553637843637004006755097640960))) (.node 1 (.leaf (0)) (.leaf (-30203757354484883176117061719865425920))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (29652090553489725492535014930461491200))) (.node 1 (.leaf (0)) (.leaf (-26029727058847196864798304998415925248)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (20354072286617356946909952780716212224))) (.node 1 (.leaf (0)) (.leaf (-14111099774168995273807094819737042944))))))

def row101Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (8623449861992163778437669056505970688))) (.node 1 (.leaf (0)) (.leaf (-4612012562099834874157084244149534720)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (2139353726284965420617403783840792576))) (.node 1 (.leaf (0)) (.leaf (-850937809332271731055519067189280768))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (285963778621366087351650432181075968))) (.node 1 (.leaf (0)) (.leaf (-79608964011808874134525395039420416)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (17864564154122608501436273781637120))) (.node 1 (.leaf (0)) (.leaf (-3104793232608990861615800325767168))))))

def row101Part06 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (392100176283094206750449010212864)) (.leaf (0)))) (.node 1 (.leaf (-32008177655762792387791755935744)) (.node 1 (.leaf (0)) (.leaf (1267650600228229401496703205376)))))

def row101 : CoefficientRow := ⟨102, (.node 48 (.node 16 row101Part00 (.node 16 row101Part01 row101Part02)) (.node 32 (.node 16 row101Part03 row101Part04) (.node 16 row101Part05 row101Part06)))⟩

theorem row101_represents : RowRepresents row101 Data.chebyshevRow101 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row102Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (5202)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4508400)) (.leaf (0))) (.node 1 (.leaf (1561108640)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-289028113920)) (.leaf (0))) (.node 1 (.leaf (33206118865920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2592089763594240)) (.leaf (0))) (.node 1 (.leaf (146125499859763200)) (.leaf (0))))))

def row102Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-6215204594035261440)) (.leaf (0))) (.node 1 (.leaf (206117307909378539520)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-5467532799280357048320)) (.leaf (0))) (.node 1 (.leaf (118392203731603229245440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2127628009089681221222400)) (.leaf (0))) (.node 1 (.leaf (32169735497435980064882688)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-413951305448488378401030144)) (.leaf (0))) (.node 1 (.leaf (4577254664844204827836678144)) (.leaf (0))))))

def row102Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-43853052756733188189273980928)) (.leaf (0))) (.node 1 (.leaf (366614647823669612491434885120)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2690835129423251251048245886976)) (.leaf (0))) (.node 1 (.leaf (17431099828440236411484654010368)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-100117086194118280927501602521088)) (.leaf (0))) (.node 1 (.leaf (511864591668418899701349656559616)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2337478896413921402441681306910720)) (.leaf (0))) (.node 1 (.leaf (9562208354991829196075438312521728)) (.leaf (0))))))

def row102Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-35129247715501897330262957772242944)) (.leaf (0))) (.node 1 (.leaf (116141594487985864642910186920476672)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-346147497297526498543575459057106944)) (.leaf (0))) (.node 1 (.leaf (931284321869655499226251235059302400)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2264109416285707915002003002637680640)) (.leaf (0))) (.node 1 (.leaf (4977479503195561139211904967686225920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-9898716300140324977415765811443793920)) (.leaf (0))) (.node 1 (.leaf (17808266976772810985282091639625482240)) (.leaf (0))))))

def row102Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-28973767700304970253831974493041459200)) (.leaf (0))) (.node 1 (.leaf (42602919965856352531741747110047907840)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-56554534669336966661978508894111006720)) (.leaf (0))) (.node 1 (.leaf (67678097388978813106881114163139051520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-72867810647288612547001888175648931840)) (.leaf (0))) (.node 1 (.leaf (70412804809116356441197677948331622400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-60876193350758842902144238057785655296)) (.leaf (0))) (.node 1 (.leaf (46908928209675645180007248373531803648)) (.leaf (0))))))

def row102Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-32064330674968162528106220407224270848)) (.leaf (0))) (.node 1 (.leaf (19329355619176832695353403569787109376)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-10202528496639521560370126955940413440)) (.leaf (0))) (.node 1 (.leaf (4672785965355556523135319432077770752)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-1835911727245234328838955179165351936)) (.leaf (0))) (.node 1 (.leaf (609678551120140239040152406564274176)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-167785401550502043806558904052088832)) (.leaf (0))) (.node 1 (.leaf (37234463396016239417149882619658240)) (.leaf (0))))))

def row102Part06 : LookupTree ℤ := (.node 3 (.node 1 (.leaf (-6401714759315072741895944731099136)) (.node 1 (.leaf (0)) (.leaf (800045985069041281019606810492928)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-64650180611639699476331863474176))) (.node 1 (.leaf (0)) (.leaf (2535301200456458802993406410752)))))

def row102 : CoefficientRow := ⟨103, (.node 48 (.node 16 row102Part00 (.node 16 row102Part01 row102Part02)) (.node 32 (.node 16 row102Part03 row102Part04) (.node 16 row102Part05 row102Part06)))⟩

theorem row102_represents : RowRepresents row102 Data.chebyshevRow102 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row103Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-103))) (.node 1 (.leaf (0)) (.leaf (182104)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-96515120))) (.node 1 (.leaf (0)) (.leaf (24321810240))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3567198835200))) (.node 1 (.leaf (0)) (.leaf (341413357608960)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-22953482657710080))) (.node 1 (.leaf (0)) (.leaf (1141115994983301120))))))

def row103Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-43563781220244848640))) (.node 1 (.leaf (0)) (.leaf (1314556205242476134400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-32075171407916417679360))) (.node 1 (.leaf (0)) (.leaf (644546132165403428782080))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-10828375020378777603538944))) (.node 1 (.leaf (0)) (.leaf (154003555845387059250331648)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1873836369153231706149355520))) (.node 1 (.leaf (0)) (.leaf (19681326509557814307168714752))))))

def row103Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-179815755837323667079132348416))) (.node 1 (.leaf (0)) (.leaf (1438526046698589336633058787328)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-10134480797462133885108576321536))) (.node 1 (.leaf (0)) (.leaf (63186641409278081712822702571520))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-350146461663121467442763854249984))) (.node 1 (.leaf (0)) (.leaf (1730956594533969247690473804398592)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-7658171600059379095842702286127104))) (.node 1 (.leaf (0)) (.leaf (30405987518459625420311635718832128))))))

def row103Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-108592812565927233643970127567257600))) (.node 1 (.leaf (0)) (.leaf (349541100212208130882237963557666816)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1015647725144906644450276346941145088))) (.node 1 (.leaf (0)) (.leaf (2667357661996724520778503537421189120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-6337481362338082320045166299436810240))) (.node 1 (.leaf (0)) (.leaf (13630585279604992950184811210945331200)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-26546123462574969876753370030496808960))) (.node 1 (.leaf (0)) (.leaf (46812518794218226449328523494639534080))))))

def row103Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-74719981921540630678735912501059256320))) (.node 1 (.leaf (0)) (.leaf (107872538350772362336736785483211735040)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-140703310892311776960961024543319654400))) (.node 1 (.leaf (0)) (.leaf (165559952132442509389879290046143528960))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-175387711848066950586538791281759354880))) (.node 1 (.leaf (0)) (.leaf (166855336677079909747193660895079170048)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-142106458988135042751198428896287522816))) (.node 1 (.leaf (0)) (.leaf (107928956193520285633821591566800650240))))))

def row103Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-72752111211928488834650109870954512384))) (.node 1 (.leaf (0)) (.leaf (43270723800453500264863891383723753472)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-22544410719564008541357657695721619456))) (.node 1 (.leaf (0)) (.leaf (10196509740043384777326157931344822272))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-3957787233111834745029560790511779840))) (.node 1 (.leaf (0)) (.leaf (1298966066252089352214830208167968768)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-353435367255126696114554081885814784))) (.node 1 (.leaf (0)) (.leaf (77573720024641469695915565565083648))))))

def row103Part06 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-13195529694913239690542338472411136))) (.node 1 (.leaf (0)) (.leaf (1632100147793845354427005376921600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-130568011823507628354160430153728))) (.node 1 (.leaf (0)) (.leaf (5070602400912917605986812821504)))))

def row103 : CoefficientRow := ⟨104, (.node 48 (.node 16 row103Part00 (.node 16 row103Part01 row103Part02)) (.node 32 (.node 16 row103Part03 row103Part04) (.node 16 row103Part05 row103Part06)))⟩

theorem row103_represents : RowRepresents row103 Data.chebyshevRow103 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row104Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-5408)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (4872608)) (.leaf (0))) (.node 1 (.leaf (-1754138880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (337671734400)) (.leaf (0))) (.node 1 (.leaf (-40340516536320)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3274916478812160)) (.leaf (0))) (.node 1 (.leaf (-192032465175183360)) (.leaf (0))))))

def row104Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8497436584001863680)) (.leaf (0))) (.node 1 (.leaf (-293244870349868236800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8096645209765309317120)) (.leaf (0))) (.node 1 (.leaf (-182542546547436064604160)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (3416720273420488078786560)) (.leaf (0))) (.node 1 (.leaf (-53826485538193535271960576)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (721958417139262496901693440)) (.leaf (0))) (.node 1 (.leaf (-8324927403150668240135389184)) (.leaf (0))))))

def row104Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (83215705775848816803611410432)) (.leaf (0))) (.node 1 (.leaf (-726246159498316946649699581952)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5567887222820429924314363461632)) (.leaf (0))) (.node 1 (.leaf (-37700061423364504181701806653440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (226490369012674444353147007664128)) (.leaf (0))) (.node 1 (.leaf (-1212157514994661834586877365059584)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5799392085481859897822628915707904)) (.leaf (0))) (.node 1 (.leaf (-24878551555110587387760842884775936)) (.leaf (0))))))

def row104Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (95941222752421148170886229209907200)) (.leaf (0))) (.node 1 (.leaf (-333327219619840331930850442054991872)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (1045229697721942760308051386172440576)) (.leaf (0))) (.node 1 (.leaf (-2962579772159468788126803928941592576)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (7598824740279156956559010077480058880)) (.leaf (0))) (.node 1 (.leaf (-17652442227871725779302237566559846400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (37159886859350310877785388233334456320)) (.leaf (0))) (.node 1 (.leaf (-70900513901922750738788831700619100160)) (.leaf (0))))))

def row104Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (122598805288741423152489021482320527360)) (.leaf (0))) (.node 1 (.leaf (-192042883808937613889213572112166420480)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (272299611370881691335452079860534476800)) (.leaf (0))) (.node 1 (.leaf (-349084719173602367028803163249778360320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (403987714912173631326760468267935989760)) (.leaf (0))) (.node 1 (.leaf (-421188228505250257614275260511850332160)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (394586866704918662396531559847943995392)) (.leaf (0))) (.node 1 (.leaf (-331121846185945730682404106166106849280)) (.leaf (0))))))

def row104Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (247922243062008733795749403540825571328)) (.leaf (0))) (.node 1 (.leaf (-164833578043033810364653623311696134144)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (96743976097546522090097909723387920384)) (.leaf (0))) (.node 1 (.leaf (-49761607404483573605850634823521009664)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (22228931207332003883491271041854996480)) (.leaf (0))) (.node 1 (.leaf (-8525253017343809729099273987587833856)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2765717534054680748236219320388026368)) (.leaf (0))) (.node 1 (.leaf (-744105197906269631646258046391287808)) (.leaf (0))))))

def row104Part06 : LookupTree ℤ := (.node 4 (.node 2 (.node 1 (.leaf (161549154808598012133727075861266432)) (.leaf (0))) (.node 1 (.leaf (-27191105374895520662104283755315200)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (3328850476199330408330342617317376)) (.leaf (0))) (.node 1 (.leaf (-263671324847471715511314266718208)) (.node 1 (.leaf (0)) (.leaf (10141204801825835211973625643008))))))

def row104 : CoefficientRow := ⟨105, (.node 48 (.node 16 row104Part00 (.node 16 row104Part01 row104Part02)) (.node 32 (.node 16 row104Part03 row104Part04) (.node 16 row104Part05 row104Part06)))⟩

theorem row104_represents : RowRepresents row104 Data.chebyshevRow104 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row105Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (105))) (.node 1 (.leaf (0)) (.leaf (-192920)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (106260336))) (.node 1 (.leaf (0)) (.leaf (-27830088000))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4242542304000))) (.node 1 (.leaf (0)) (.leaf (-422094390681600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (29503315615334400))) (.node 1 (.leaf (0)) (.leaf (-1525180925333667840))))))

def row105Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (60558654388248576000))) (.node 1 (.leaf (0)) (.leaf (-1901045945942212608000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (48268461827447036313600))) (.node 1 (.leaf (0)) (.leaf (-1009631225260275557990400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (17661815567219753761112064))) (.node 1 (.leaf (0)) (.leaf (-261656526921774129794252800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3317753203431756699952742400))) (.node 1 (.leaf (0)) (.leaf (-36331181315859150787439493120))))))

def row105Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (346247167389021300686355169280))) (.node 1 (.leaf (0)) (.leaf (-2891018365695223229932457951232)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (21270255243102993733737303244800))) (.node 1 (.leaf (0)) (.leaf (-138586764256007090076226315878400))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (803127199688470356149057869578240))) (.node 1 (.leaf (0)) (.leaf (-4155271624523292916864228534517760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (19256955771023098891487960117542912))) (.node 1 (.leaf (0)) (.leaf (-80163090628680800195833321488384000))))))

def row105Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (300475258070769529985742585987072000))) (.node 1 (.leaf (0)) (.leaf (-1016195539451888794743938847667650560)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (3106107120588792165066379119286026240))) (.node 1 (.leaf (0)) (.leaf (-8592517206315662097032111395304374272))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (21535130842896396233163186454396928000))) (.node 1 (.leaf (0)) (.leaf (-48935469735348444508789286344065024000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (100865897181275591632324146497165721600))) (.node 1 (.leaf (0)) (.leaf (-188613546598063727926906186895877734400))))))

def row105Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (319917592499023476983713955465700311040))) (.node 1 (.leaf (0)) (.leaf (-491958305968647590115163929707544576000)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (685302533634075159631865184264388608000))) (.node 1 (.leaf (0)) (.leaf (-863729390479647243447485616545700249600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (983363141672414213240059727817631334400))) (.node 1 (.leaf (0)) (.leaf (-1009231793687580424975744181918779834368)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (931280192397972367544261548592175513600))) (.node 1 (.leaf (0)) (.leaf (-770172648565411746998629803899014348800))))))

def row105Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (568596597335945956426148916952605655040))) (.node 1 (.leaf (0)) (.leaf (-372937879886521120994171138007116021760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (216032362914657052721553477142497460224))) (.node 1 (.leaf (0)) (.leaf (-109719724549010531989027427578386841600))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (48415649647775842512012102874221772800))) (.node 1 (.leaf (0)) (.leaf (-18349472100939708810413378183343636480)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (5884870435364488192586992722661867520))) (.node 1 (.leaf (0)) (.leaf (-1565784115837180732988431658347659264))))))

def row105Part06 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (0)) (.leaf (336293839312109263957996490194944000))) (.node 1 (.leaf (0)) (.node 1 (.leaf (-56014310897584886678635572887552000)) (.leaf (0))))) (.node 2 (.node 1 (.leaf (6788268964222168445014845664788480)) (.leaf (0))) (.node 1 (.leaf (-532413252095856348628615346257920)) (.node 1 (.leaf (0)) (.leaf (20282409603651670423947251286016))))))

def row105 : CoefficientRow := ⟨106, (.node 48 (.node 16 row105Part00 (.node 16 row105Part01 row105Part02)) (.node 32 (.node 16 row105Part03 row105Part04) (.node 16 row105Part05 row105Part06)))⟩

theorem row105_represents : RowRepresents row105 Data.chebyshevRow105 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row106Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (5618)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-5258448)) (.leaf (0))) (.node 1 (.leaf (1966659552)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-393331910400)) (.leaf (0))) (.node 1 (.leaf (48825601144320)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-4119105260175360)) (.leaf (0))) (.node 1 (.leaf (251039096405852160)) (.leaf (0))))))

def row106Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-11547798434669199360)) (.leaf (0))) (.node 1 (.leaf (414362179126365388800)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-11898737101649734533120)) (.leaf (0))) (.node 1 (.leaf (279079470202330137231360)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-5435982723941039194767360)) (.leaf (0))) (.node 1 (.leaf (89150116672633042794184704)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1245271470982810756490199040)) (.leaf (0))) (.node 1 (.leaf (14960433810014181640040873984)) (.leaf (0))))))

def row106Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-155878068407567118378490396672)) (.leaf (0))) (.node 1 (.leaf (1418740494276359548022409920512)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-11349923954210876384179279364096)) (.leaf (0))) (.node 1 (.leaf (80240571909570491649176413143040)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-503663897524688624505599639420928)) (.leaf (0))) (.node 1 (.leaf (2818411914371602546884993104216064)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-14109935334528445731551085984743424)) (.leaf (0))) (.node 1 (.leaf (63392463097156785170736763119861760)) (.leaf (0))))))

def row106Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-256267404009782748562552872186675200)) (.leaf (0))) (.node 1 (.leaf (934277735761379391902335614029135872)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3077620776625720349795929081507741696)) (.leaf (0))) (.node 1 (.leaf (9174794013337053118259562167513645056)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-24783859152910481150623232868088807424)) (.leaf (0))) (.node 1 (.leaf (60722703913664518245628610475353702400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-135030826330047199895363960921464504320)) (.leaf (0))) (.node 1 (.leaf (272632308264473934003437124694950543360)) (.leaf (0))))))

def row106Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-499825898484868879006301395274075996160)) (.leaf (0))) (.node 1 (.leaf (831878068806984567856641483043567042560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1256216223308176871565779939275623628800)) (.leaf (0))) (.node 1 (.leaf (1719689786441752686292533531778555576320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2131446495871468118221731701359336488960)) (.leaf (0))) (.node 1 (.leaf (2387914511850078684094394716147113000960)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-2413050454080079512348019923685503664128)) (.leaf (0))) (.node 1 (.leaf (2193682230981890465770927203350457876480)) (.leaf (0))))))

def row106Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1788267540192832227793009011338854268928)) (.leaf (0))) (.node 1 (.leaf (1302026772714925723216951457216907444224)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-842619735870588764078440185737619963904)) (.leaf (0))) (.node 1 (.leaf (481826333233797679048957589108515930112)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-241668380305353067861546126198628679680)) (.leaf (0))) (.node 1 (.leaf (105356552312895494753123479736031379456)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-39464661735934098369062975687075299328)) (.leaf (0))) (.node 1 (.leaf (12513846068635246016820243491715022848)) (.leaf (0))))))

def row106Part06 : LookupTree ℤ := (.node 5 (.node 2 (.node 1 (.leaf (-3293117386482959478110590392556584960)) (.leaf (0))) (.node 1 (.leaf (699778783999114048578097264145203200)) (.node 1 (.leaf (0)) (.leaf (-115357472271369103765601488392421376))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (13840209253291808605541005596295168)) (.leaf (0)))) (.node 1 (.leaf (-1074967708993538532469204318158848)) (.node 1 (.leaf (0)) (.leaf (40564819207303340847894502572032))))))

def row106 : CoefficientRow := ⟨107, (.node 48 (.node 16 row106Part00 (.node 16 row106Part01 row106Part02)) (.node 32 (.node 16 row106Part03 row106Part04) (.node 16 row106Part05 row106Part06)))⟩

theorem row106_represents : RowRepresents row106 Data.chebyshevRow106 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row107Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-107))) (.node 1 (.leaf (0)) (.leaf (204156)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-116777232))) (.node 1 (.leaf (0)) (.leaf (31763407104))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-5029206124800))) (.node 1 (.leaf (0)) (.leaf (519745592970240)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-37741526135685120))) (.node 1 (.leaf (0)) (.leaf (2027259118145372160))))))

def row107Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-83654251257586974720))) (.node 1 (.leaf (0)) (.leaf (2729770304194943385600)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-72065936030746505379840))) (.node 1 (.leaf (0)) (.leaf (1567790165664935832453120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-28533781015101832150646784))) (.node 1 (.leaf (0)) (.leaf (439956760267040215382622208)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5808296145397378212933140480))) (.node 1 (.leaf (0)) (.leaf (66252048935887514067521241088))))))

def row107Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-658003304204155537443335962624))) (.node 1 (.leaf (0)) (.leaf (5728499354247942325977277792256)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-43970103151524746502095861972992))) (.node 1 (.leaf (0)) (.leaf (299067908075148073374579142164480))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1810454994737847605160257148420096))) (.node 1 (.leaf (0)) (.leaf (9792095453266498010634214742949888)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-47476826440079990354590132087029760))) (.node 1 (.leaf (0)) (.leaf (206948016822994370537306847728107520))))))

def row107Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-813010066090335027110848330360422400))) (.node 1 (.leaf (0)) (.leaf (2884751010974647578548610075725922304)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-9261348673840232864658237282301509632))) (.node 1 (.leaf (0)) (.leaf (26942105232989768333551235730331664384))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-71102849148717358534409652190574542848))) (.node 1 (.leaf (0)) (.leaf (170380877562677481000046507294772428800)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-370927549841369991423052068340094730240))) (.node 1 (.leaf (0)) (.leaf (733878163127011595933780436285778821120))))))

def row107Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1319569389468761234996316746013852303360))) (.node 1 (.leaf (0)) (.leaf (2155714443582616725828446895794678661120)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-3197734980250428902763425062815635865600))) (.node 1 (.leaf (0)) (.leaf (4303108963363152616032552680102811402240))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-5246256133415350449683523130536304312320))) (.node 1 (.leaf (0)) (.leaf (5785060817387737793164533614213005836288)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-5757381100558131392240301395963182841856))) (.node 1 (.leaf (0)) (.leaf (5157537110529192678540484210599930101760))))))

def row107Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4145131677721610412012166939630314192896))) (.node 1 (.leaf (0)) (.leaf (2976991425316372567428074052440930910208)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-1901271834655834580878433848617737388032))) (.node 1 (.leaf (0)) (.leaf (1073372391016605890086942605795418701824))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-531752410258481978235104355271479132160))) (.node 1 (.leaf (0)) (.leaf (229062576726730698316660337655406395392)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-84814193907232684930712944096812466176))) (.node 1 (.leaf (0)) (.leaf (26593476253107672766628918641777704960))))))

def row107Part06 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (-6922528612278028220179177275308113920)) (.leaf (0)))) (.node 1 (.leaf (1455571878895812983834830101177958400)) (.node 1 (.leaf (0)) (.leaf (-237503213506960375976217822449631232))))) (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (28212831758679473559710626538848256)) (.leaf (0)))) (.node 1 (.leaf (-2170217827590728735362355887603712)) (.node 1 (.leaf (0)) (.leaf (81129638414606681695789005144064))))))

def row107 : CoefficientRow := ⟨108, (.node 48 (.node 16 row107Part00 (.node 16 row107Part01 row107Part02)) (.node 32 (.node 16 row107Part03 row107Part04) (.node 16 row107Part05 row107Part06)))⟩

theorem row107_represents : RowRepresents row107 Data.chebyshevRow107 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row108Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1)) (.leaf (0))) (.node 1 (.leaf (-5832)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5666760)) (.leaf (0))) (.node 1 (.leaf (-2200214016)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (456858724608)) (.leaf (0))) (.node 1 (.leaf (-58884013393920)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5158596446115840)) (.leaf (0))) (.node 1 (.leaf (-326522148677222400)) (.leaf (0))))))

def row108Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (15602316670959943680)) (.leaf (0))) (.node 1 (.leaf (-581670681641539338240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (17358277710039621304320)) (.leaf (0))) (.node 1 (.leaf (-423211342263823147991040)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (8571563055270910859673600)) (.leaf (0))) (.node 1 (.leaf (-146217678702836707095478272)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (2125184991516891187255443456)) (.leaf (0))) (.node 1 (.leaf (-26577026100808938065907154944)) (.leaf (0))))))

def row108Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (288382166279342146513532878848)) (.leaf (0))) (.node 1 (.leaf (-2734747102684670622909081845760)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (22806922662706761036133834948608)) (.leaf (0))) (.node 1 (.leaf (-168180778212619984653368137089024)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (1101799713674984771254757923749888)) (.leaf (0))) (.node 1 (.leaf (-6439321903847297757205507401056256)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (33694126241061441752819515470643200)) (.leaf (0))) (.node 1 (.leaf (-158346115977316765879917027293921280)) (.leaf (0))))))

def row108Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (670163437655771489637166567642890240)) (.leaf (0))) (.node 1 (.leaf (-2560297867942049446124032274749980672)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (8847122798575015506893149232959586304)) (.leaf (0))) (.node 1 (.leaf (-27697491361017518847576036732116664320)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (78668069618890017817725704328752136192)) (.leaf (0))) (.node 1 (.leaf (-202928402211099235314447914856502788096)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (475792581455402161895456975511009361920)) (.leaf (0))) (.node 1 (.leaf (-1014487407947213916849541261375140003840)) (.leaf (0))))))

def row108Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1967582224738892070873862267845633638400)) (.leaf (0))) (.node 1 (.leaf (-3471016847744507037849274975071271649280)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (5567645110473410323222673730864980951040)) (.leaf (0))) (.node 1 (.leaf (-8115159746942610491819383657409827307520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (10737664422597773350286837061564959293440)) (.leaf (0))) (.node 1 (.leaf (-12880426778680779583461440977219721625600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (13983172088855555098677087152111515336704)) (.leaf (0))) (.node 1 (.leaf (-13708444432098153250251529995276823560192)) (.leaf (0))))))

def row108Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (12103341761251217584873977432538714472448)) (.leaf (0))) (.node 1 (.leaf (-9592290128158146547241285336477535830016)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (6796602586503333898934588290619481784320)) (.leaf (0))) (.node 1 (.leaf (-4284370002545466840805825286343990706176)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (2388413162338564848035431337789466083328)) (.leaf (0))) (.node 1 (.leaf (-1168861372829859451223332190278989643776)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (497589815189395495002383650997888090112)) (.leaf (0))) (.node 1 (.leaf (-182142233883100615878246131685339955200)) (.leaf (0))))))

def row108Part06 : LookupTree ℤ := (.node 6 (.node 3 (.node 1 (.leaf (56480069892698305011368427676111994880)) (.node 1 (.leaf (0)) (.leaf (-14544836008555170488936451814761431040)))) (.node 1 (.leaf (0)) (.node 1 (.leaf (3026501230062995071435261690748338176)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-488846636267212560557976650495557632)) (.node 1 (.leaf (0)) (.leaf (57500631226352485651890457395855360)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4381000474388760811572606277779456))) (.node 1 (.leaf (0)) (.leaf (162259276829213363391578010288128))))))

def row108 : CoefficientRow := ⟨109, (.node 48 (.node 16 row108Part00 (.node 16 row108Part01 row108Part02)) (.node 32 (.node 16 row108Part03 row108Part04) (.node 16 row108Part05 row108Part06)))⟩

theorem row108_represents : RowRepresents row108 Data.chebyshevRow108 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row109Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (109))) (.node 1 (.leaf (0)) (.leaf (-215820)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (128110752))) (.node 1 (.leaf (0)) (.leaf (-36163835136))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5942923574016))) (.node 1 (.leaf (0)) (.leaf (-637513619758080)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (48058719027916800))) (.node 1 (.leaf (0)) (.leaf (-2680303415499816960))))))

def row109Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (114858884599506862080))) (.node 1 (.leaf (0)) (.leaf (-3893111667478022062080)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (106782491450825747988480))) (.node 1 (.leaf (0)) (.leaf (-2414212850192582128435200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (45676907125643653869993984))) (.node 1 (.leaf (0)) (.leaf (-732392117672713629573578752)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (10058666128431160587444027392))) (.node 1 (.leaf (0)) (.leaf (-119406101137505390199335550976))))))

def row109Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (1234767636762839830470401720320))) (.node 1 (.leaf (0)) (.leaf (-11197993559617283571795441483776)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (89583948476938268574363531870208))) (.node 1 (.leaf (0)) (.leaf (-635429464500388042681315416342528))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (4014054422087817147669772995919872))) (.node 1 (.leaf (0)) (.leaf (-22670739260961093525045229545062400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (114865078922202873860229163028316160))) (.node 1 (.leaf (0)) (.leaf (-523640248777627902297140902315950080))))))

def row109Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (2153336941401878006385181465646202880))) (.node 1 (.leaf (0)) (.leaf (-8005346746858746470796674625225883648)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (26955594270990263878444535748220682240))) (.node 1 (.leaf (0)) (.leaf (-82337087955024806028703309194564993024))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (228438988386497394169861060848078815232))) (.node 1 (.leaf (0)) (.leaf (-576237681984875951628942337007778004992)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1322512712752174315213966019362113454080))) (.node 1 (.leaf (0)) (.leaf (-2762852979021439429632862959036058828800))))))

def row109Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5254733838946545376744041281705119580160))) (.node 1 (.leaf (0)) (.leaf (-9097748139071630801526996845937221959680)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (14333025201197249549208772524545597767680))) (.node 1 (.leaf (0)) (.leaf (-20533428457248373599671319994922466017280))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (26721584978610897150257197253666222899200))) (.node 1 (.leaf (0)) (.leaf (-31545914374749296960087415568652449087488)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (33723725278269241589594475700186213515264))) (.node 1 (.leaf (0)) (.leaf (-32574425974725499179043544201153577222144))))))

def row109Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (28351815200224045581760121804707743137792))) (.node 1 (.leaf (0)) (.leaf (-22161571681632665661910644725396002570240)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (15494477007662502378747610429856700956672))) (.node 1 (.leaf (0)) (.leaf (-9642112396107539571698593178483400114176))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (5308578734935611674305967030850411298816))) (.node 1 (.leaf (0)) (.leaf (-2566785322386449600763324718213385682944)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (1079993824286023674935480246092588646400))) (.node 1 (.leaf (0)) (.leaf (-390877944019308904523121182012457615360))))))

def row109Part06 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (0)) (.node 1 (.leaf (119882668397674638242916032627532103680)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-30545243896006153961707733730700820480)) (.leaf (0))) (.node 1 (.leaf (6290505673632950518846741203946307584)) (.leaf (0))))) (.node 3 (.node 1 (.leaf (-1005906104293104594675663927529963520)) (.node 1 (.leaf (0)) (.leaf (117171480280295700039143270679314432)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-8843130587192128304841001560702976))) (.node 1 (.leaf (0)) (.leaf (324518553658426726783156020576256))))))

def row109 : CoefficientRow := ⟨110, (.node 48 (.node 16 row109Part00 (.node 16 row109Part01 row109Part02)) (.node 32 (.node 16 row109Part03 row109Part04) (.node 16 row109Part05 row109Part06)))⟩

theorem row109_represents : RowRepresents row109 Data.chebyshevRow109 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row110Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1)) (.leaf (0))) (.node 1 (.leaf (6050)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6098400)) (.leaf (0))) (.node 1 (.leaf (2456435520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-529186394880)) (.leaf (0))) (.node 1 (.leaf (70769860541952)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-6433623685632000)) (.leaf (0))) (.node 1 (.leaf (422639586733056000)) (.leaf (0))))))

def row110Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-20962923501959577600)) (.leaf (0))) (.node 1 (.leaf (811388450840553062400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-25144501044995665428480)) (.leaf (0))) (.node 1 (.leaf (636776325165474643968000)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-13399988755656075116544000)) (.leaf (0))) (.node 1 (.leaf (237571492954124014835466240)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-3589969226862318446402600960)) (.leaf (0))) (.node 1 (.leaf (46694358357671259240795209728)) (.leaf (0))))))

def row110Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-527194368554352926912203980800)) (.leaf (0))) (.node 1 (.leaf (5204282376210350283849885286400)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-45202909781941328179724717916160)) (.leaf (0))) (.node 1 (.leaf (347348675166496521802095200829440)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-2372658642675760856617388756434944)) (.leaf (0))) (.node 1 (.leaf (14467430748022932052545053392896000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-79035604762983628802909974560768000)) (.leaf (0))) (.node 1 (.leaf (388076273821722513600375353350553600)) (.leaf (0))))))

def row110Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-1717443935211027294231448372274790400)) (.leaf (0))) (.node 1 (.leaf (6866971750745805458894395206042386432)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-24857816292292508448486498483411353600)) (.leaf (0))) (.node 1 (.leaf (81608679902998046604465108228558028800)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-243342245528939629875132322717882122240)) (.leaf (0))) (.node 1 (.leaf (659806378984094023654170036552660418560)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-1628267945425154065153341649526565371904)) (.leaf (0))) (.node 1 (.leaf (3659512833451562547277473300099366912000)) (.leaf (0))))))

def row110Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-7493288182781770930139588185917751296000)) (.leaf (0))) (.node 1 (.leaf (13980484525637597791337357538481510809600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-23763141388616671926276667422739424870400)) (.leaf (0))) (.node 1 (.leaf (36781210149337109590236928706501022842880)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-51804521337094520549629477051409891328000)) (.leaf (0))) (.node 1 (.leaf (66323596735902573883975835484552167424000)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-77075000838354149018851918289416413511680)) (.leaf (0))) (.node 1 (.leaf (81155894988636636429440481395649250590720)) (.leaf (0))))))

def row110Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-77252193710702215942961065834845868916736)) (.leaf (0))) (.node 1 (.leaf (66295920528606237710761528945893022105600)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-51119745949768665222755877741411486924800)) (.leaf (0))) (.node 1 (.leaf (35273324017870471598301046146057392619520)) (.leaf (0))))) (.node 4 (.node 2 (.node 1 (.leaf (-21672637954553643991432617694756266311680)) (.leaf (0))) (.node 1 (.leaf (11786018842701082799835266251979812241408)) (.leaf (0)))) (.node 2 (.node 1 (.leaf (-5631160459962294696529033087424659456000)) (.leaf (0))) (.node 1 (.leaf (2342129882455147965749206623870517248000)) (.leaf (0))))))

def row110Part06 : LookupTree ℤ := (.node 7 (.node 3 (.node 1 (.leaf (-838235957931316114057610791701027225600)) (.node 1 (.leaf (0)) (.leaf (254310172803904446974768517069825638400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-64116989022075302994850729152149979136))) (.node 1 (.leaf (0)) (.leaf (13069857983533113598251459058388172800))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2069312839812561675003218312455782400))) (.node 1 (.leaf (0)) (.leaf (238723961034980160889859147636408320)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-17848520451213469973073581131694080))) (.node 1 (.leaf (0)) (.leaf (649037107316853453566312041152512))))))

def row110 : CoefficientRow := ⟨111, (.node 48 (.node 16 row110Part00 (.node 16 row110Part01 row110Part02)) (.node 32 (.node 16 row110Part03 row110Part04) (.node 16 row110Part05 row110Part06)))⟩

theorem row110_represents : RowRepresents row110 Data.chebyshevRow110 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

def row111Part00 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-111))) (.node 1 (.leaf (0)) (.leaf (227920)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-140307552))) (.node 1 (.leaf (0)) (.leaf (41076706176))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-7001296363776))) (.node 1 (.leaf (0)) (.leaf (779053340841984)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-60925966399180800))) (.node 1 (.leaf (0)) (.leaf (3525582588965928960))))))

def row111Part01 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-156784731603426017280))) (.node 1 (.leaf (0)) (.leaf (5515888569159128186880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-157071493540817078845440))) (.node 1 (.leaf (0)) (.leaf (3687765500523531416371200))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-72476884636955804103081984))) (.node 1 (.leaf (0)) (.leaf (1207535103580961659244511232)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-17238604582155797480249229312))) (.node 1 (.leaf (0)) (.leaf (212794817852847908680925970432))))))

def row111Part02 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-2289156373871545684294809681920))) (.node 1 (.leaf (0)) (.leaf (21606558312037984139495212056576)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-179989768040820924933812967702528))) (.node 1 (.leaf (0)) (.leaf (1330126814833381086285505818001408))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-8759371707439338860904550508789760))) (.node 1 (.leaf (0)) (.leaf (51605600757006957630135336330854400)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-272936288448170131466049112149852160))) (.node 1 (.leaf (0)) (.leaf (1299792796421072929497891609017057280))))))

def row111Part03 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-5588224811823932594848078210195783680))) (.node 1 (.leaf (0)) (.leaf (21739290248350357388585465037310656512)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-76671226855575280775417532715043389440))) (.node 1 (.leaf (0)) (.leaf (245554447761020899237633525651681050624))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-715123479444376653920125706283843059712))) (.node 1 (.leaf (0)) (.leaf (1895850439953063998937282410113098842112)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-4579048603602482445520649318415244197888))) (.node 1 (.leaf (0)) (.leaf (10081878645924564524187809559234792652800))))))

def row111Part04 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-20241310204510087237023217653540622172160))) (.node 1 (.leaf (0)) (.leaf (37058717190346826384201711922900243578880)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-61859307978430593401762107370024447508480))) (.node 1 (.leaf (0)) (.leaf (94095848755922592780145177407924511703040))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-130330627652799938249516151356486005555200))) (.node 1 (.leaf (0)) (.leaf (164193107846554444728039086537756783935488)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-187873726954977539627298312279019040538624))) (.node 1 (.leaf (0)) (.leaf (194886215951998772037924506992452078403584))))))

def row111Part05 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-182856202621628477467682253474399480971264))) (.node 1 (.leaf (0)) (.leaf (154753412738845141083433702617182046781440)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-117733968907199832824259365912679674806272))) (.node 1 (.leaf (0)) (.leaf (80188760431848482768300685470598185353216))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-48653854644042899657171202420362943922176))) (.node 1 (.leaf (0)) (.leaf (26138823007788615200433857222173010165760)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-12342314744210613067993546420941907558400))) (.node 1 (.leaf (0)) (.leaf (5075137708929604836021534429753492111360))))))

def row111Part06 : LookupTree ℤ := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-1796354584260306866358137616029586554880))) (.node 1 (.leaf (0)) (.leaf (539165589503815047911244767870352097280)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-134524483717783556508548199508246265856))) (.node 1 (.leaf (0)) (.leaf (27145622071359331791178582044306309120))))) (.node 4 (.node 2 (.node 1 (.leaf (0)) (.leaf (-4255797159905419050045579895590879232))) (.node 1 (.leaf (0)) (.leaf (486291052657152450084559296833519616)))) (.node 2 (.node 1 (.leaf (0)) (.leaf (-36021559456085366672930318283964416))) (.node 1 (.leaf (0)) (.leaf (1298074214633706907132624082305024))))))

def row111 : CoefficientRow := ⟨112, (.node 48 (.node 16 row111Part00 (.node 16 row111Part01 row111Part02)) (.node 32 (.node 16 row111Part03 row111Part04) (.node 16 row111Part05 row111Part06)))⟩

theorem row111_represents : RowRepresents row111 Data.chebyshevRow111 := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · rfl
  · rfl

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.CoefficientCache
