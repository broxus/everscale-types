#[test]
fn test_ser_de_rayon() {
    use crate::boc::Boc;

    let data = include_bytes!("block.boc.2");
    let cell = Boc::decode(data).unwrap();

    let data_serial = Boc::encode(&cell);
    let data_parallel = Boc::encode_par(&cell);

    assert_eq!(data_serial, data_parallel);
    assert_eq!(data.as_slice(), data_serial.as_slice());
}
